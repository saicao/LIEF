/* Copyright 2022 - 2026 R. Thomas
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include "LIEF/DyldSharedCache/DyldSharedCache.hpp"
#include "LIEF/DyldSharedCache/Dylib.hpp"
#include "LIEF/DyldSharedCache/MappingInfo.hpp"
#include "LIEF/DyldSharedCache/SubCache.hpp"
#include "LIEF/DyldSharedCache/caching.hpp"
#include "LIEF/DyldSharedCache/utils.hpp"

#include "LIEF/BinaryStream/FileStream.hpp"
#include "LIEF/MachO/Binary.hpp"
#include "LIEF/MachO/BinaryParser.hpp"
#include "LIEF/MachO/ParserConfig.hpp"
#include "LIEF/MachO/enums.hpp"

#include "MachO/Structures.hpp"

#include "logging.hpp"
#include "internal_utils.hpp"

#include <algorithm>
#include <array>
#include <cstring>
#include <filesystem>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

// NOLINTBEGIN

namespace LIEF::dsc {
namespace {

namespace fs = std::filesystem;

template<class T>
struct dyld_it {
  dyld_it() = default;
  dyld_it(const details::DyldSharedCache* cache, size_t idx) :
    cache(cache),
    idx(idx) {}

  const details::DyldSharedCache* cache = nullptr;
  size_t idx = 0;
};

struct dyld_cache_header {
  char magic[16];
  uint32_t mappingOffset;
  uint32_t mappingCount;
  uint32_t imagesOffsetOld;
  uint32_t imagesCountOld;
  uint64_t dyldBaseAddress;
  uint64_t codeSignatureOffset;
  uint64_t codeSignatureSize;
  uint64_t slideInfoOffsetUnused;
  uint64_t slideInfoSizeUnused;
  uint64_t localSymbolsOffset;
  uint64_t localSymbolsSize;
  uint8_t uuid[16];
  uint64_t cacheType;
  uint32_t branchPoolsOffset;
  uint32_t branchPoolsCount;
  uint64_t dyldInCacheMH;
  uint64_t dyldInCacheEntry;
  uint64_t imagesTextOffset;
  uint64_t imagesTextCount;
  uint64_t patchInfoAddr;
  uint64_t patchInfoSize;
  uint64_t otherImageGroupAddrUnused;
  uint64_t otherImageGroupSizeUnused;
  uint64_t progClosuresAddr;
  uint64_t progClosuresSize;
  uint64_t progClosuresTrieAddr;
  uint64_t progClosuresTrieSize;
  uint32_t platform;
  uint32_t flags;
  uint64_t sharedRegionStart;
  uint64_t sharedRegionSize;
  uint64_t maxSlide;
  uint64_t dylibsImageArrayAddr;
  uint64_t dylibsImageArraySize;
  uint64_t dylibsTrieAddr;
  uint64_t dylibsTrieSize;
  uint64_t otherImageArrayAddr;
  uint64_t otherImageArraySize;
  uint64_t otherTrieAddr;
  uint64_t otherTrieSize;
  uint32_t mappingWithSlideOffset;
  uint32_t mappingWithSlideCount;
  uint64_t dylibsPBLStateArrayAddrUnused;
  uint64_t dylibsPBLSetAddr;
  uint64_t programsPBLSetPoolAddr;
  uint64_t programsPBLSetPoolSize;
  uint64_t programTrieAddr;
  uint32_t programTrieSize;
  uint32_t osVersion;
  uint32_t altPlatform;
  uint32_t altOsVersion;
  uint64_t swiftOptsOffset;
  uint64_t swiftOptsSize;
  uint32_t subCacheArrayOffset;
  uint32_t subCacheArrayCount;
  uint8_t symbolFileUUID[16];
  uint64_t rosettaReadOnlyAddr;
  uint64_t rosettaReadOnlySize;
  uint64_t rosettaReadWriteAddr;
  uint64_t rosettaReadWriteSize;
  uint32_t imagesOffset;
  uint32_t imagesCount;
  uint32_t cacheSubType;
  uint64_t objcOptsOffset;
  uint64_t objcOptsSize;
  uint64_t cacheAtlasOffset;
  uint64_t cacheAtlasSize;
  uint64_t dynamicDataOffset;
  uint64_t dynamicDataMaxSize;
  uint32_t tproMappingsOffset;
  uint32_t tproMappingsCount;
  uint64_t functionVariantInfoAddr;
  uint64_t functionVariantInfoSize;
  uint64_t prewarmingDataOffset;
  uint64_t prewarmingDataSize;
};

struct dyld_cache_mapping_info {
  uint64_t address;
  uint64_t size;
  uint64_t fileOffset;
  uint32_t maxProt;
  uint32_t initProt;
};

struct dyld_cache_image_info {
  uint64_t address;
  uint64_t modTime;
  uint64_t inode;
  uint32_t pathFileOffset;
  uint32_t pad;
};

struct dyld_subcache_entry_v1 {
  uint8_t uuid[16];
  uint64_t cacheVMOffset;
};

struct dyld_subcache_entry {
  uint8_t uuid[16];
  uint64_t cacheVMOffset;
  char fileSuffix[32];
};

struct mapping_t {
  uint64_t address = 0;
  uint64_t size = 0;
  uint64_t file_offset = 0;
  uint32_t max_prot = 0;
  uint32_t init_prot = 0;
  size_t file_idx = 0;

  uint64_t end_address() const {
    return address + size;
  }

  bool contains(uint64_t va) const {
    return address <= va && va < end_address();
  }
};

struct image_t {
  uint64_t address = 0;
  uint64_t modtime = 0;
  uint64_t inode = 0;
  uint32_t path_file_offset = 0;
  std::string path;
};

struct subcache_t {
  sc_uuid_t uuid = {};
  uint64_t vm_offset = 0;
  std::string suffix;
  std::string path;
};

struct cache_file_t {
  std::string path;
  std::string filename;
  std::unique_ptr<FileStream> stream;
  dyld_cache_header header = {};
};

static bool checked_add(uint64_t lhs, uint64_t rhs, uint64_t& out) {
  if (lhs > std::numeric_limits<uint64_t>::max() - rhs) {
    return false;
  }
  out = lhs + rhs;
  return true;
}

static uint64_t align(uint64_t value, uint64_t alignment) {
  const uint64_t rem = value % alignment;
  return rem == 0 ? value : value + (alignment - rem);
}

static std::string trim_nulls_and_spaces(std::string value) {
  while (!value.empty() && (value.back() == '\0' || value.back() == ' ')) {
    value.pop_back();
  }
  const size_t first = value.find_first_not_of(' ');
  if (first == std::string::npos) {
    return "";
  }
  return value.substr(first);
}

static std::string basename(const std::string& path) {
  return fs::path(path).filename().string();
}

static std::string cstr(const char* ptr, size_t max_size) {
  const size_t len = strnlen(ptr, max_size);
  return std::string(ptr, len);
}

static bool uuid_is_null(const uint8_t uuid[16]) {
  return std::all_of(uuid, uuid + 16, [] (uint8_t c) { return c == 0; });
}

static sc_uuid_t to_uuid(const uint8_t uuid[16]) {
  sc_uuid_t out = {};
  std::copy(uuid, uuid + 16, out.begin());
  return out;
}

static bool header_has_field(const dyld_cache_header& header, size_t offset,
                             size_t size = 1) {
  uint64_t end_offset = 0;
  return checked_add(offset, size, end_offset) &&
         end_offset <= header.mappingOffset;
}

template<class T>
static result<T> peek(FileStream& stream, uint64_t offset) {
  T value = {};
  if (!stream.peek_in(&value, offset, sizeof(T))) {
    return make_error_code(lief_errors::read_error);
  }
  return value;
}

static result<std::string> peek_string(FileStream& stream, uint64_t offset,
                                       size_t max_size = 4096) {
  return stream.peek_string_at(offset, max_size);
}

static std::string arch_from_magic(const dyld_cache_header& header) {
  std::string magic(header.magic, sizeof(header.magic));
  magic = trim_nulls_and_spaces(std::move(magic));
  const size_t pos = magic.find_last_of(' ');
  if (pos == std::string::npos) {
    return "";
  }
  return trim_nulls_and_spaces(magic.substr(pos + 1));
}

static dsc::DyldSharedCache::DYLD_TARGET_ARCH arch_enum_from_name(
    const std::string& arch)
{
  if (arch == "i386") {
    return dsc::DyldSharedCache::DYLD_TARGET_ARCH::I386;
  }
  if (arch == "x86_64") {
    return dsc::DyldSharedCache::DYLD_TARGET_ARCH::X86_64;
  }
  if (arch == "x86_64h") {
    return dsc::DyldSharedCache::DYLD_TARGET_ARCH::X86_64H;
  }
  if (arch == "arm64") {
    return dsc::DyldSharedCache::DYLD_TARGET_ARCH::ARM64;
  }
  if (arch == "arm64e") {
    return dsc::DyldSharedCache::DYLD_TARGET_ARCH::ARM64E;
  }
  return dsc::DyldSharedCache::DYLD_TARGET_ARCH::UNKNOWN;
}

static bool is_main_cache_filename(const fs::path& path,
                                   const std::string& arch) {
  const std::string name = path.filename().string();
  constexpr std::string_view PREFIX = "dyld_shared_cache_";
  if (name.rfind(PREFIX, 0) != 0) {
    return false;
  }
  if (!arch.empty()) {
    return name == (std::string(PREFIX) + arch);
  }
  const std::string suffix = name.substr(PREFIX.size());
  return !suffix.empty() && suffix.find('.') == std::string::npos;
}

static std::optional<std::string> find_main_cache(const std::string& path,
                                                  const std::string& arch) {
  std::error_code ec;
  fs::path p(path);
  if (fs::is_regular_file(p, ec)) {
    return p.string();
  }
  if (!fs::is_directory(p, ec)) {
    return std::nullopt;
  }

  std::vector<fs::path> candidates;
  for (const fs::directory_entry& entry : fs::directory_iterator(p, ec)) {
    if (ec) {
      break;
    }
    if (!entry.is_regular_file(ec)) {
      continue;
    }
    if (is_main_cache_filename(entry.path(), arch)) {
      candidates.push_back(entry.path());
    }
  }
  if (candidates.empty()) {
    return std::nullopt;
  }
  std::sort(candidates.begin(), candidates.end());
  return candidates.front().string();
}

static bool is_segment_command(uint32_t cmd) {
  using LIEF::MachO::LoadCommand;
  return cmd == static_cast<uint32_t>(LoadCommand::TYPE::SEGMENT) ||
         cmd == static_cast<uint32_t>(LoadCommand::TYPE::SEGMENT_64);
}

static bool is_linkedit_data_command(uint32_t cmd) {
  using LIEF::MachO::LoadCommand;
  switch (static_cast<LoadCommand::TYPE>(cmd)) {
    case LoadCommand::TYPE::CODE_SIGNATURE:
    case LoadCommand::TYPE::SEGMENT_SPLIT_INFO:
    case LoadCommand::TYPE::FUNCTION_STARTS:
    case LoadCommand::TYPE::DATA_IN_CODE:
    case LoadCommand::TYPE::DYLIB_CODE_SIGN_DRS:
    case LoadCommand::TYPE::LINKER_OPTIMIZATION_HINT:
    case LoadCommand::TYPE::DYLD_EXPORTS_TRIE:
    case LoadCommand::TYPE::DYLD_CHAINED_FIXUPS:
      return true;
    default:
      return false;
  }
}

static bool is_linkedit_segment(const char segname[16]) {
  return cstr(segname, 16) == "__LINKEDIT";
}

static void add_delta_u32(uint32_t& value, int64_t delta) {
  if (value == 0) {
    return;
  }
  const int64_t new_value = static_cast<int64_t>(value) + delta;
  value = new_value > 0 ? static_cast<uint32_t>(new_value) : 0;
}

static void add_delta_u64(uint64_t& value, int64_t delta) {
  if (value == 0) {
    return;
  }
  const int64_t new_value = static_cast<int64_t>(value) + delta;
  value = new_value > 0 ? static_cast<uint64_t>(new_value) : 0;
}

static result<uint64_t> parse_magic_version(const dyld_cache_header& header) {
  std::string magic(header.magic, sizeof(header.magic));
  if (magic.rfind("dyld_v", 0) != 0 || magic.size() < 7) {
    return make_error_code(lief_errors::parsing_error);
  }
  if (magic[6] < '0' || magic[6] > '9') {
    return make_error_code(lief_errors::parsing_error);
  }
  return static_cast<uint64_t>(magic[6] - '0');
}

}

namespace details {

class DyldSharedCache {
  public:
  static std::unique_ptr<DyldSharedCache> parse(const std::string& path,
                                                const std::string& arch);

  std::string filename() const {
    return main_file().filename;
  }

  std::string filepath() const {
    return main_file().path;
  }

  uint64_t load_address() const {
    if (header_has_field(main_file().header,
                         offsetof(dyld_cache_header, sharedRegionStart),
                         sizeof(uint64_t)) &&
        main_file().header.sharedRegionStart != 0)
    {
      return main_file().header.sharedRegionStart;
    }
    if (!mappings_.empty()) {
      return mappings_.front().address;
    }
    return 0;
  }

  std::string arch_name() const {
    return arch_name_;
  }

  dsc::DyldSharedCache::DYLD_TARGET_ARCH arch() const {
    return arch_;
  }

  dsc::DyldSharedCache::DYLD_TARGET_PLATFORM platform() const {
    if (!header_has_field(main_file().header, offsetof(dyld_cache_header, platform),
                          sizeof(uint32_t))) {
      return dsc::DyldSharedCache::DYLD_TARGET_PLATFORM::UNKNOWN;
    }
    return static_cast<dsc::DyldSharedCache::DYLD_TARGET_PLATFORM>(
        main_file().header.platform
    );
  }

  FileStream& stream() const {
    return *main_file().stream;
  }

  result<uint64_t> va_to_offset(uint64_t va) const {
    const mapping_t* mapping = mapping_from_va(va);
    if (mapping == nullptr) {
      return make_error_code(lief_errors::not_found);
    }
    return mapping->file_offset + (va - mapping->address);
  }

  const cache_file_t* cache_file_for_va(uint64_t va) const {
    const mapping_t* mapping = mapping_from_va(va);
    if (mapping == nullptr || mapping->file_idx >= files_.size()) {
      return nullptr;
    }
    return files_[mapping->file_idx].get();
  }

  ok_error_t read_va(uint64_t va, std::vector<uint8_t>& out,
                     uint64_t size) const {
    out.clear();
    if (size == 0) {
      return ok();
    }
    out.resize(size, 0);
    return read_va(va, out.data(), size);
  }

  ok_error_t read_va(uint64_t va, uint8_t* dst, uint64_t size) const {
    uint64_t copied = 0;
    while (copied < size) {
      const uint64_t cur_va = va + copied;
      const mapping_t* mapping = mapping_from_va(cur_va);
      if (mapping == nullptr || mapping->file_idx >= files_.size()) {
        return make_error_code(lief_errors::not_found);
      }
      const uint64_t available = mapping->end_address() - cur_va;
      const uint64_t chunk_size = std::min<uint64_t>(available, size - copied);
      const uint64_t offset = mapping->file_offset + (cur_va - mapping->address);
      if (!files_[mapping->file_idx]->stream->peek_in(dst + copied, offset,
                                                      chunk_size)) {
        return make_error_code(lief_errors::read_error);
      }
      copied += chunk_size;
    }
    return ok();
  }

  const image_t* image_at(size_t idx) const {
    if (idx >= images_.size()) {
      return nullptr;
    }
    return &images_[idx];
  }

  const mapping_t* mapping_at(size_t idx) const {
    if (idx >= mappings_.size()) {
      return nullptr;
    }
    return &mappings_[idx];
  }

  const subcache_t* subcache_at(size_t idx) const {
    if (idx >= subcaches_.size()) {
      return nullptr;
    }
    return &subcaches_[idx];
  }

  size_t images_count() const {
    return images_.size();
  }

  size_t mappings_count() const {
    return mappings_.size();
  }

  size_t subcaches_count() const {
    return subcaches_.size();
  }

  std::unique_ptr<MachO::Binary> extract(
      const image_t& image, const dsc::Dylib::extract_opt_t& opt) const;

  const image_t* find_image_from_va(uint64_t va) const {
    auto it = std::find_if(images_.begin(), images_.end(),
      [va] (const image_t& image) {
        return image.address == va;
      }
    );
    return it == images_.end() ? nullptr : &*it;
  }

  const image_t* find_image_from_path(const std::string& path) const {
    auto it = std::find_if(images_.begin(), images_.end(),
      [&path] (const image_t& image) {
        return image.path == path;
      }
    );
    return it == images_.end() ? nullptr : &*it;
  }

  const image_t* find_image_from_name(const std::string& name) const {
    auto it = std::find_if(images_.begin(), images_.end(),
      [&name] (const image_t& image) {
        return image.path == name || basename(image.path) == name;
      }
    );
    return it == images_.end() ? nullptr : &*it;
  }

  std::unique_ptr<dsc::DyldSharedCache> load_cache_for_file(size_t file_idx) const {
    if (file_idx >= files_.size()) {
      return nullptr;
    }
    return dsc::DyldSharedCache::from_path(files_[file_idx]->path);
  }

  std::unique_ptr<dsc::DyldSharedCache> load_cache_from_path(
      const std::string& path) const
  {
    return dsc::DyldSharedCache::from_path(path);
  }

  private:
  const cache_file_t& main_file() const {
    return *files_.front();
  }

  cache_file_t& main_file() {
    return *files_.front();
  }

  const mapping_t* mapping_from_va(uint64_t va) const {
    auto it = std::find_if(mappings_.begin(), mappings_.end(),
      [va] (const mapping_t& mapping) {
        return mapping.contains(va);
      }
    );
    return it == mappings_.end() ? nullptr : &*it;
  }

  ok_error_t parse_file(const std::string& path, bool main_file);
  ok_error_t parse_mappings(size_t file_idx);
  ok_error_t parse_images(size_t file_idx);
  ok_error_t parse_subcaches();
  std::optional<std::string> subcache_path_from_suffix(
      const std::string& suffix) const;

  std::vector<std::unique_ptr<cache_file_t>> files_;
  std::vector<mapping_t> mappings_;
  std::vector<image_t> images_;
  std::vector<subcache_t> subcaches_;
  std::string arch_name_;
  dsc::DyldSharedCache::DYLD_TARGET_ARCH arch_ =
      dsc::DyldSharedCache::DYLD_TARGET_ARCH::UNKNOWN;
};

class Dylib {
  public:
  Dylib(const DyldSharedCache* cache, image_t image) :
    cache_(cache),
    image_(std::move(image)) {}

  const DyldSharedCache* cache_ = nullptr;
  image_t image_;
};

class DylibIt : public dyld_it<Dylib> {
  public:
  using dyld_it<Dylib>::dyld_it;
};

class MappingInfo {
  public:
  MappingInfo(const DyldSharedCache* cache, mapping_t mapping) :
    cache_(cache),
    mapping_(mapping) {}

  const DyldSharedCache* cache_ = nullptr;
  mapping_t mapping_;
};

class MappingInfoIt : public dyld_it<MappingInfo> {
  public:
  using dyld_it<MappingInfo>::dyld_it;
};

class SubCache {
  public:
  SubCache(const DyldSharedCache* cache, subcache_t subcache) :
    cache_(cache),
    subcache_(std::move(subcache)) {}

  const DyldSharedCache* cache_ = nullptr;
  subcache_t subcache_;
};

class SubCacheIt : public dyld_it<SubCache> {
  public:
  using dyld_it<SubCache>::dyld_it;
};

std::unique_ptr<DyldSharedCache> DyldSharedCache::parse(
    const std::string& path, const std::string& arch)
{
  std::optional<std::string> main_path = find_main_cache(path, arch);
  if (!main_path) {
    LIEF_ERR("Can't find a dyld shared cache in '{}'", path);
    return nullptr;
  }

  auto cache = std::unique_ptr<DyldSharedCache>(new DyldSharedCache{});
  if (!cache->parse_file(*main_path, true)) {
    return nullptr;
  }

  cache->arch_name_ = arch_from_magic(cache->main_file().header);
  cache->arch_ = arch_enum_from_name(cache->arch_name_);

  if (!cache->parse_subcaches()) {
    LIEF_WARN("Failed to parse subcaches for '{}'", *main_path);
  }

  return cache;
}

ok_error_t DyldSharedCache::parse_file(const std::string& path, bool main) {
  auto stream = FileStream::from_file(path);
  if (!stream) {
    return make_error_code(lief_errors::read_error);
  }

  auto file = std::make_unique<cache_file_t>();
  file->path = path;
  file->filename = basename(path);
  file->stream = std::make_unique<FileStream>(std::move(*stream));

  auto header = peek<dyld_cache_header>(*file->stream, 0);
  if (!header) {
    LIEF_ERR("Can't read dyld shared cache header in '{}'", path);
    return make_error_code(lief_errors::read_error);
  }
  if (std::string(header->magic, header->magic + 4) != "dyld") {
    LIEF_ERR("'{}' is not a dyld shared cache", path);
    return make_error_code(lief_errors::file_format_error);
  }
  if (!parse_magic_version(*header)) {
    LIEF_ERR("'{}' has an unsupported dyld shared cache magic", path);
    return make_error_code(lief_errors::file_format_error);
  }
  file->header = *header;

  const size_t file_idx = files_.size();
  files_.push_back(std::move(file));

  if (!parse_mappings(file_idx)) {
    return make_error_code(lief_errors::parsing_error);
  }

  if (main) {
    if (!parse_images(file_idx)) {
      return make_error_code(lief_errors::parsing_error);
    }
  }
  return ok();
}

ok_error_t DyldSharedCache::parse_mappings(size_t file_idx) {
  if (file_idx >= files_.size()) {
    return make_error_code(lief_errors::not_found);
  }

  const cache_file_t& file = *files_[file_idx];
  const dyld_cache_header& header = file.header;

  if (header.mappingOffset == 0 || header.mappingCount == 0) {
    return ok();
  }

  uint64_t end_offset = 0;
  if (!checked_add(header.mappingOffset,
                   uint64_t(header.mappingCount) * sizeof(dyld_cache_mapping_info),
                   end_offset) ||
      end_offset > file.stream->size())
  {
    LIEF_WARN("Mapping table is out of bounds in '{}'", file.path);
    return make_error_code(lief_errors::read_out_of_bound);
  }

  for (uint32_t i = 0; i < header.mappingCount; ++i) {
    const uint64_t offset = header.mappingOffset +
                            uint64_t(i) * sizeof(dyld_cache_mapping_info);
    auto raw_mapping = peek<dyld_cache_mapping_info>(*file.stream, offset);
    if (!raw_mapping) {
      return make_error_code(lief_errors::read_error);
    }
    mapping_t mapping;
    mapping.address = raw_mapping->address;
    mapping.size = raw_mapping->size;
    mapping.file_offset = raw_mapping->fileOffset;
    mapping.max_prot = raw_mapping->maxProt;
    mapping.init_prot = raw_mapping->initProt;
    mapping.file_idx = file_idx;
    mappings_.push_back(mapping);
  }

  std::sort(mappings_.begin(), mappings_.end(),
    [] (const mapping_t& lhs, const mapping_t& rhs) {
      return lhs.address < rhs.address;
    }
  );

  return ok();
}

ok_error_t DyldSharedCache::parse_images(size_t file_idx) {
  if (file_idx >= files_.size()) {
    return make_error_code(lief_errors::not_found);
  }

  const cache_file_t& file = *files_[file_idx];
  const dyld_cache_header& header = file.header;

  uint32_t images_offset = header.imagesOffsetOld;
  uint32_t images_count = header.imagesCountOld;
  if (header_has_field(header, offsetof(dyld_cache_header, imagesCount),
                       sizeof(uint32_t)) &&
      header.imagesOffset != 0)
  {
    images_offset = header.imagesOffset;
    images_count = header.imagesCount;
  }

  if (images_offset == 0 || images_count == 0) {
    return ok();
  }

  uint64_t end_offset = 0;
  if (!checked_add(images_offset,
                   uint64_t(images_count) * sizeof(dyld_cache_image_info),
                   end_offset) ||
      end_offset > file.stream->size())
  {
    LIEF_WARN("Images table is out of bounds in '{}'", file.path);
    return make_error_code(lief_errors::read_out_of_bound);
  }

  images_.reserve(images_.size() + images_count);
  for (uint32_t i = 0; i < images_count; ++i) {
    const uint64_t offset = images_offset +
                            uint64_t(i) * sizeof(dyld_cache_image_info);
    auto raw_image = peek<dyld_cache_image_info>(*file.stream, offset);
    if (!raw_image) {
      return make_error_code(lief_errors::read_error);
    }

    image_t image;
    image.address = raw_image->address;
    image.modtime = raw_image->modTime;
    image.inode = raw_image->inode;
    image.path_file_offset = raw_image->pathFileOffset;

    if (auto path = peek_string(*file.stream, raw_image->pathFileOffset)) {
      image.path = *path;
    }
    images_.push_back(std::move(image));
  }

  std::sort(images_.begin(), images_.end(),
    [] (const image_t& lhs, const image_t& rhs) {
      return lhs.address < rhs.address;
    }
  );

  return ok();
}

std::optional<std::string> DyldSharedCache::subcache_path_from_suffix(
    const std::string& suffix) const
{
  if (suffix.empty()) {
    return std::nullopt;
  }
  fs::path main_path(main_file().path);
  return (main_path.parent_path() /
          (main_path.filename().string() + suffix)).string();
}

ok_error_t DyldSharedCache::parse_subcaches() {
  dyld_cache_header& header = main_file().header;
  if (!header_has_field(header, offsetof(dyld_cache_header, subCacheArrayCount),
                        sizeof(uint32_t)) ||
      header.subCacheArrayOffset == 0 || header.subCacheArrayCount == 0)
  {
    return ok();
  }

  const bool has_suffix =
      header_has_field(header, offsetof(dyld_cache_header, cacheSubType),
                       sizeof(uint32_t));
  const uint64_t entry_size = has_suffix ? sizeof(dyld_subcache_entry) :
                                           sizeof(dyld_subcache_entry_v1);

  uint64_t end_offset = 0;
  if (!checked_add(header.subCacheArrayOffset,
                   uint64_t(header.subCacheArrayCount) * entry_size,
                   end_offset) ||
      end_offset > main_file().stream->size())
  {
    LIEF_WARN("Subcache table is out of bounds in '{}'", main_file().path);
    return make_error_code(lief_errors::read_out_of_bound);
  }

  for (uint32_t i = 0; i < header.subCacheArrayCount; ++i) {
    const uint64_t offset = header.subCacheArrayOffset + uint64_t(i) * entry_size;
    subcache_t subcache;
    if (has_suffix) {
      auto entry = peek<dyld_subcache_entry>(stream(), offset);
      if (!entry) {
        return make_error_code(lief_errors::read_error);
      }
      subcache.uuid = to_uuid(entry->uuid);
      subcache.vm_offset = entry->cacheVMOffset;
      subcache.suffix = cstr(entry->fileSuffix, sizeof(entry->fileSuffix));
      if (auto path = subcache_path_from_suffix(subcache.suffix)) {
        subcache.path = *path;
      }
    } else {
      auto entry = peek<dyld_subcache_entry_v1>(stream(), offset);
      if (!entry) {
        return make_error_code(lief_errors::read_error);
      }
      subcache.uuid = to_uuid(entry->uuid);
      subcache.vm_offset = entry->cacheVMOffset;
      subcache.suffix = "." + std::to_string(i + 1);
      if (auto path = subcache_path_from_suffix(subcache.suffix)) {
        subcache.path = *path;
      }
    }

    if (!subcache.path.empty()) {
      std::error_code ec;
      if (fs::is_regular_file(subcache.path, ec)) {
        if (!parse_file(subcache.path, false)) {
          LIEF_WARN("Failed to parse subcache '{}'", subcache.path);
        }
      } else {
        LIEF_WARN("Can't find subcache '{}'", subcache.path);
      }
    }
    subcaches_.push_back(std::move(subcache));
  }

  if (header_has_field(header, offsetof(dyld_cache_header, symbolFileUUID), 16) &&
      !uuid_is_null(header.symbolFileUUID))
  {
    fs::path symbols_path = fs::path(main_file().path).parent_path() /
                            (fs::path(main_file().path).filename().string() +
                             ".symbols");
    std::error_code ec;
    if (fs::is_regular_file(symbols_path, ec)) {
      subcache_t subcache;
      subcache.uuid = to_uuid(header.symbolFileUUID);
      subcache.suffix = ".symbols";
      subcache.path = symbols_path.string();
      if (!parse_file(subcache.path, false)) {
        LIEF_WARN("Failed to parse symbols cache '{}'", subcache.path);
      }
      subcaches_.push_back(std::move(subcache));
    }
  }

  return ok();
}

std::unique_ptr<MachO::Binary> DyldSharedCache::extract(
    const image_t& image, const dsc::Dylib::extract_opt_t& opt) const
{
  if (opt.fix_branches || opt.fix_memory || opt.fix_relocations ||
      opt.fix_objc || opt.create_dyld_chained_fixup_cmd)
  {
    LIEF_WARN("Enhanced dyld shared cache de-optimization is not implemented; "
              "performing raw extraction");
  }

  std::vector<uint8_t> header_data;
  if (!read_va(image.address, header_data, sizeof(MachO::details::mach_header_64))) {
    return nullptr;
  }

  const uint32_t magic = *reinterpret_cast<const uint32_t*>(header_data.data());
  using LIEF::MachO::MACHO_TYPES;
  const bool is64 = magic == static_cast<uint32_t>(MACHO_TYPES::MAGIC_64) ||
                    magic == static_cast<uint32_t>(MACHO_TYPES::CIGAM_64);
  const bool is32 = magic == static_cast<uint32_t>(MACHO_TYPES::MAGIC) ||
                    magic == static_cast<uint32_t>(MACHO_TYPES::CIGAM);
  if (!is64 && !is32) {
    LIEF_ERR("Dylib '{}' does not start with a valid Mach-O header", image.path);
    return nullptr;
  }
  if (magic == static_cast<uint32_t>(MACHO_TYPES::CIGAM) ||
      magic == static_cast<uint32_t>(MACHO_TYPES::CIGAM_64))
  {
    LIEF_ERR("Big-endian Mach-O images in dyld shared cache are not supported");
    return nullptr;
  }

  uint32_t sizeofcmds = 0;
  uint32_t ncmds = 0;
  uint64_t header_size = 0;
  if (is64) {
    MachO::details::mach_header_64 hdr = {};
    std::memcpy(&hdr, header_data.data(), sizeof(hdr));
    sizeofcmds = hdr.sizeofcmds;
    ncmds = hdr.ncmds;
    header_size = sizeof(hdr);
  } else {
    MachO::details::mach_header hdr = {};
    std::memcpy(&hdr, header_data.data(), sizeof(hdr));
    sizeofcmds = hdr.sizeofcmds;
    ncmds = hdr.ncmds;
    header_size = sizeof(hdr);
  }

  uint64_t load_commands_end = 0;
  if (!checked_add(header_size, sizeofcmds, load_commands_end) ||
      load_commands_end > 16 * 1024 * 1024)
  {
    LIEF_ERR("Mach-O load commands for '{}' are out of bounds", image.path);
    return nullptr;
  }

  if (!read_va(image.address, header_data, load_commands_end)) {
    return nullptr;
  }

  struct write_t {
    uint64_t vmaddr = 0;
    uint64_t fileoff = 0;
    uint64_t size = 0;
  };

  std::vector<write_t> writes;
  int64_t linkedit_delta = 0;
  uint64_t data_head = 0;
  uint64_t cmd_offset = header_size;

  for (uint32_t i = 0; i < ncmds; ++i) {
    if (cmd_offset + sizeof(MachO::details::load_command) > header_data.size()) {
      LIEF_ERR("Corrupted Mach-O load command in '{}'", image.path);
      return nullptr;
    }

    auto* lc = reinterpret_cast<MachO::details::load_command*>(
        header_data.data() + cmd_offset
    );
    if (lc->cmdsize < sizeof(MachO::details::load_command) ||
        cmd_offset + lc->cmdsize > header_data.size())
    {
      LIEF_ERR("Corrupted Mach-O load command size in '{}'", image.path);
      return nullptr;
    }

    if (is_segment_command(lc->cmd)) {
      if (lc->cmd == static_cast<uint32_t>(MachO::LoadCommand::TYPE::SEGMENT_64)) {
        if (lc->cmdsize < sizeof(MachO::details::segment_command_64)) {
          return nullptr;
        }
        auto* seg = reinterpret_cast<MachO::details::segment_command_64*>(
            header_data.data() + cmd_offset
        );

        const uint64_t old_fileoff = seg->fileoff;
        const uint64_t new_fileoff = data_head;
        const int64_t delta = static_cast<int64_t>(new_fileoff) -
                              static_cast<int64_t>(old_fileoff);

        writes.push_back({seg->vmaddr, new_fileoff, seg->filesize});
        seg->fileoff = new_fileoff;

        auto* sections = reinterpret_cast<MachO::details::section_64*>(
            header_data.data() + cmd_offset + sizeof(*seg)
        );
        for (uint32_t n = 0; n < seg->nsects; ++n) {
          add_delta_u32(sections[n].offset, delta);
        }

        if (is_linkedit_segment(seg->segname)) {
          linkedit_delta = delta;
        }
        data_head = align(new_fileoff + seg->filesize, 0x4000);
      } else {
        if (lc->cmdsize < sizeof(MachO::details::segment_command_32)) {
          return nullptr;
        }
        auto* seg = reinterpret_cast<MachO::details::segment_command_32*>(
            header_data.data() + cmd_offset
        );

        const uint64_t old_fileoff = seg->fileoff;
        const uint64_t new_fileoff = data_head;
        const int64_t delta = static_cast<int64_t>(new_fileoff) -
                              static_cast<int64_t>(old_fileoff);

        writes.push_back({seg->vmaddr, new_fileoff, seg->filesize});
        seg->fileoff = static_cast<uint32_t>(new_fileoff);

        auto* sections = reinterpret_cast<MachO::details::section_32*>(
            header_data.data() + cmd_offset + sizeof(*seg)
        );
        for (uint32_t n = 0; n < seg->nsects; ++n) {
          add_delta_u32(sections[n].offset, delta);
        }

        if (is_linkedit_segment(seg->segname)) {
          linkedit_delta = delta;
        }
        data_head = align(new_fileoff + seg->filesize, 0x4000);
      }
    }

    cmd_offset += lc->cmdsize;
  }

  cmd_offset = header_size;
  for (uint32_t i = 0; i < ncmds; ++i) {
    auto* lc = reinterpret_cast<MachO::details::load_command*>(
        header_data.data() + cmd_offset
    );

    if (is_linkedit_data_command(lc->cmd)) {
      auto* cmd = reinterpret_cast<MachO::details::linkedit_data_command*>(
          header_data.data() + cmd_offset
      );
      add_delta_u32(cmd->dataoff, linkedit_delta);
    } else if (lc->cmd == static_cast<uint32_t>(
                           MachO::LoadCommand::TYPE::DYLD_INFO) ||
               lc->cmd == static_cast<uint32_t>(
                           MachO::LoadCommand::TYPE::DYLD_INFO_ONLY))
    {
      auto* cmd = reinterpret_cast<MachO::details::dyld_info_command*>(
          header_data.data() + cmd_offset
      );
      add_delta_u32(cmd->rebase_off, linkedit_delta);
      add_delta_u32(cmd->bind_off, linkedit_delta);
      add_delta_u32(cmd->weak_bind_off, linkedit_delta);
      add_delta_u32(cmd->lazy_bind_off, linkedit_delta);
      add_delta_u32(cmd->export_off, linkedit_delta);
    } else if (lc->cmd == static_cast<uint32_t>(
                           MachO::LoadCommand::TYPE::SYMTAB))
    {
      auto* cmd = reinterpret_cast<MachO::details::symtab_command*>(
          header_data.data() + cmd_offset
      );
      add_delta_u32(cmd->symoff, linkedit_delta);
      add_delta_u32(cmd->stroff, linkedit_delta);
    } else if (lc->cmd == static_cast<uint32_t>(
                           MachO::LoadCommand::TYPE::DYSYMTAB))
    {
      auto* cmd = reinterpret_cast<MachO::details::dysymtab_command*>(
          header_data.data() + cmd_offset
      );
      add_delta_u32(cmd->tocoff, linkedit_delta);
      add_delta_u32(cmd->modtaboff, linkedit_delta);
      add_delta_u32(cmd->extrefsymoff, linkedit_delta);
      add_delta_u32(cmd->indirectsymoff, linkedit_delta);
      add_delta_u32(cmd->extreloff, linkedit_delta);
      add_delta_u32(cmd->locreloff, linkedit_delta);
    } else if (lc->cmd == static_cast<uint32_t>(
                           MachO::LoadCommand::TYPE::ROUTINES_64))
    {
      auto* cmd = reinterpret_cast<MachO::details::routines_command_64*>(
          header_data.data() + cmd_offset
      );
      add_delta_u64(cmd->init_address, linkedit_delta);
    }

    cmd_offset += lc->cmdsize;
  }

  uint64_t output_size = header_data.size();
  for (const write_t& write : writes) {
    uint64_t write_end = 0;
    if (!checked_add(write.fileoff, write.size, write_end)) {
      return nullptr;
    }
    output_size = std::max(output_size, write_end);
  }

  std::vector<uint8_t> output(output_size, 0);
  for (const write_t& write : writes) {
    if (write.size == 0) {
      continue;
    }
    if (!read_va(write.vmaddr, output.data() + write.fileoff, write.size)) {
      LIEF_WARN("Can't read segment at VA {:#x} for '{}'", write.vmaddr,
                image.path);
    }
  }

  std::copy(header_data.begin(), header_data.end(), output.begin());

  MachO::ParserConfig conf = MachO::ParserConfig::deep();
  conf.from_dyld_shared_cache = true;
  auto bin = MachO::BinaryParser::parse(output, conf);
  if (bin == nullptr) {
    return nullptr;
  }
  return bin;
}

}

// ----------------------------------------------------------------------------
// utils
// ----------------------------------------------------------------------------
bool is_shared_cache(BinaryStream& stream) {
  std::array<char, 4> magic = {};
  if (!stream.peek_in(magic.data(), 0, magic.size())) {
    return false;
  }
  return std::string(magic.data(), magic.size()) == "dyld";
}

// ----------------------------------------------------------------------------
// caching
// ----------------------------------------------------------------------------
bool enable_cache() {
  return false;
}

bool enable_cache(const std::string&) {
  return false;
}

// ----------------------------------------------------------------------------
// DyldSharedCache/DyldSharedCache.hpp
// ----------------------------------------------------------------------------
DyldSharedCache::DyldSharedCache(std::unique_ptr<details::DyldSharedCache> impl) :
  impl_(std::move(impl)) {}

DyldSharedCache::~DyldSharedCache() = default;

std::unique_ptr<DyldSharedCache> DyldSharedCache::from_path(const std::string& path,
                                                            const std::string& arch) {
  auto impl = details::DyldSharedCache::parse(path, arch);
  if (impl == nullptr) {
    return nullptr;
  }
  return std::make_unique<DyldSharedCache>(std::move(impl));
}

std::unique_ptr<DyldSharedCache>
    DyldSharedCache::from_files(const std::vector<std::string>& files) {
  if (files.empty()) {
    return nullptr;
  }
  return from_path(files.front());
}

std::string DyldSharedCache::filename() const {
  return impl_ == nullptr ? "" : impl_->filename();
}

DyldSharedCache::VERSION DyldSharedCache::version() const {
  return VERSION::UNKNOWN;
}

std::string DyldSharedCache::filepath() const {
  return impl_ == nullptr ? "" : impl_->filepath();
}

uint64_t DyldSharedCache::load_address() const {
  return impl_ == nullptr ? 0 : impl_->load_address();
}

std::string DyldSharedCache::arch_name() const {
  return impl_ == nullptr ? "" : impl_->arch_name();
}

DyldSharedCache::DYLD_TARGET_PLATFORM DyldSharedCache::platform() const {
  return impl_ == nullptr ? DYLD_TARGET_PLATFORM::UNKNOWN : impl_->platform();
}

DyldSharedCache::DYLD_TARGET_ARCH DyldSharedCache::arch() const {
  return impl_ == nullptr ? DYLD_TARGET_ARCH::UNKNOWN : impl_->arch();
}

std::unique_ptr<Dylib> DyldSharedCache::find_lib_from_va(uint64_t va) const {
  if (impl_ == nullptr) {
    return nullptr;
  }
  const image_t* image = impl_->find_image_from_va(va);
  if (image == nullptr) {
    return nullptr;
  }
  return std::make_unique<Dylib>(
      std::make_unique<details::Dylib>(impl_.get(), *image)
  );
}

std::unique_ptr<Dylib>
    DyldSharedCache::find_lib_from_path(const std::string& path) const {
  if (impl_ == nullptr) {
    return nullptr;
  }
  const image_t* image = impl_->find_image_from_path(path);
  if (image == nullptr) {
    return nullptr;
  }
  return std::make_unique<Dylib>(
      std::make_unique<details::Dylib>(impl_.get(), *image)
  );
}

std::unique_ptr<Dylib>
    DyldSharedCache::find_lib_from_name(const std::string& name) const {
  if (impl_ == nullptr) {
    return nullptr;
  }
  const image_t* image = impl_->find_image_from_name(name);
  if (image == nullptr) {
    return nullptr;
  }
  return std::make_unique<Dylib>(
      std::make_unique<details::Dylib>(impl_.get(), *image)
  );
}

bool DyldSharedCache::has_subcaches() const {
  return impl_ != nullptr && impl_->subcaches_count() > 0;
}

DyldSharedCache::instructions_iterator
    DyldSharedCache::disassemble(uint64_t /*va*/) const {
  return make_range<assembly::Instruction::Iterator>(
      assembly::Instruction::Iterator(), assembly::Instruction::Iterator()
  );
}

std::vector<uint8_t>
    DyldSharedCache::get_content_from_va(uint64_t va,
                                         uint64_t size) const {
  if (impl_ == nullptr) {
    return {};
  }
  std::vector<uint8_t> content;
  if (!impl_->read_va(va, content, size)) {
    return {};
  }
  return content;
}

std::unique_ptr<DyldSharedCache>
    DyldSharedCache::cache_for_address(uint64_t va) const {
  if (impl_ == nullptr) {
    return nullptr;
  }
  const cache_file_t* file = impl_->cache_file_for_va(va);
  if (file == nullptr) {
    return nullptr;
  }
  return DyldSharedCache::from_path(file->path);
}

std::unique_ptr<DyldSharedCache> DyldSharedCache::main_cache() const {
  if (impl_ == nullptr) {
    return nullptr;
  }
  return DyldSharedCache::from_path(impl_->filepath());
}

std::unique_ptr<DyldSharedCache>
    DyldSharedCache::find_subcache(const std::string& filename) const {
  if (impl_ == nullptr) {
    return nullptr;
  }
  for (size_t i = 0; i < impl_->subcaches_count(); ++i) {
    const subcache_t* subcache = impl_->subcache_at(i);
    if (subcache == nullptr) {
      continue;
    }
    if (basename(subcache->path) == filename || subcache->suffix == filename) {
      return DyldSharedCache::from_path(subcache->path);
    }
  }
  return nullptr;
}

result<uint64_t> DyldSharedCache::va_to_offset(uint64_t va) const {
  if (impl_ == nullptr) {
    return make_error_code(lief_errors::not_found);
  }
  return impl_->va_to_offset(va);
}

DyldSharedCache::dylib_iterator DyldSharedCache::libraries() const {
  if (impl_ == nullptr) {
    return make_empty_iterator<Dylib>();
  }
  return make_range<Dylib::Iterator>(
      Dylib::Iterator(std::make_unique<details::DylibIt>(
          details::DylibIt{impl_.get(), 0})),
      Dylib::Iterator(std::make_unique<details::DylibIt>(
          details::DylibIt{impl_.get(), impl_->images_count()}))
  );
}

FileStream& DyldSharedCache::stream() const {
  return impl_->stream();
}

FileStream& DyldSharedCache::stream() {
  return impl_->stream();
}

DyldSharedCache::mapping_info_iterator DyldSharedCache::mapping_info() const {
  if (impl_ == nullptr) {
    return make_empty_iterator<MappingInfo>();
  }
  return make_range<MappingInfo::Iterator>(
      MappingInfo::Iterator(std::make_unique<details::MappingInfoIt>(
          details::MappingInfoIt{impl_.get(), 0})),
      MappingInfo::Iterator(std::make_unique<details::MappingInfoIt>(
          details::MappingInfoIt{impl_.get(), impl_->mappings_count()}))
  );
}

DyldSharedCache::subcache_iterator DyldSharedCache::subcaches() const {
  if (impl_ == nullptr) {
    return make_empty_iterator<SubCache>();
  }
  return make_range<SubCache::Iterator>(
      SubCache::Iterator(std::make_unique<details::SubCacheIt>(
          details::SubCacheIt{impl_.get(), 0})),
      SubCache::Iterator(std::make_unique<details::SubCacheIt>(
          details::SubCacheIt{impl_.get(), impl_->subcaches_count()}))
  );
}

void DyldSharedCache::enable_caching(const std::string&) const {}
void DyldSharedCache::flush_cache() const {}

// ----------------------------------------------------------------------------
// DyldSharedCache/Dylib.hpp
// ----------------------------------------------------------------------------
Dylib::Iterator::Iterator() = default;

Dylib::Dylib::extract_opt_t::extract_opt_t() = default;

Dylib::Iterator::Iterator(std::unique_ptr<details::DylibIt> impl) :
  impl_(std::move(impl)) {}

Dylib::Iterator::Iterator(Dylib::Iterator&&) noexcept = default;
Dylib::Iterator& Dylib::Iterator::operator=(Dylib::Iterator&&) noexcept = default;

Dylib::Iterator::Iterator(const Dylib::Iterator& other) :
  impl_(other.impl_ == nullptr ? nullptr :
        std::make_unique<details::DylibIt>(*other.impl_)) {}

Dylib::Iterator& Dylib::Iterator::operator=(const Dylib::Iterator& other) {
  if (this == &other) {
    return *this;
  }
  impl_ = other.impl_ == nullptr ? nullptr :
          std::make_unique<details::DylibIt>(*other.impl_);
  cached_.reset();
  return *this;
}

Dylib::Iterator::~Iterator() = default;

bool Dylib::Iterator::operator<(const Dylib::Iterator& rhs) const {
  return impl_ != nullptr && rhs.impl_ != nullptr && impl_->idx < rhs.impl_->idx;
}

std::ptrdiff_t Dylib::Iterator::operator-(const Iterator& rhs) const {
  if (impl_ == nullptr || rhs.impl_ == nullptr) {
    return 0;
  }
  return static_cast<std::ptrdiff_t>(impl_->idx) -
         static_cast<std::ptrdiff_t>(rhs.impl_->idx);
}

Dylib::Iterator& Dylib::Iterator::operator+=(std::ptrdiff_t n) {
  if (impl_ != nullptr) {
    impl_->idx += n;
    cached_.reset();
  }
  return *this;
}

Dylib::Iterator& Dylib::Iterator::operator-=(std::ptrdiff_t n) {
  return *this += -n;
}

bool operator==(const Dylib::Iterator& lhs, const Dylib::Iterator& rhs) {
  if (lhs.impl_ == nullptr || rhs.impl_ == nullptr) {
    return lhs.impl_ == nullptr && rhs.impl_ == nullptr;
  }
  return lhs.impl_->cache == rhs.impl_->cache && lhs.impl_->idx == rhs.impl_->idx;
}

void Dylib::Iterator::load() const {
  if (cached_ != nullptr || impl_ == nullptr || impl_->cache == nullptr) {
    return;
  }
  const image_t* image = impl_->cache->image_at(impl_->idx);
  if (image == nullptr) {
    return;
  }
  cached_ = std::make_unique<Dylib>(
      std::make_unique<details::Dylib>(impl_->cache, *image)
  );
}

const Dylib& Dylib::Iterator::operator*() const {
  load();
  return *cached_;
}

const Dylib* Dylib::Iterator::operator->() const {
  load();
  return cached_.get();
}

std::unique_ptr<Dylib> Dylib::Iterator::yield() {
  load();
  return std::move(cached_);
}

Dylib::Dylib(std::unique_ptr<details::Dylib> impl) :
  impl_(std::move(impl)) {}

Dylib::~Dylib() = default;

std::unique_ptr<LIEF::MachO::Binary>
    Dylib::get(const Dylib::extract_opt_t& opt) const {
  if (impl_ == nullptr || impl_->cache_ == nullptr) {
    return nullptr;
  }
  return impl_->cache_->extract(impl_->image_, opt);
}

std::string Dylib::path() const {
  return impl_ == nullptr ? "" : impl_->image_.path;
}

uint64_t Dylib::address() const {
  return impl_ == nullptr ? 0 : impl_->image_.address;
}

uint64_t Dylib::modtime() const {
  return impl_ == nullptr ? 0 : impl_->image_.modtime;
}

uint64_t Dylib::inode() const {
  return impl_ == nullptr ? 0 : impl_->image_.inode;
}

uint64_t Dylib::padding() const {
  return 0;
}

// ----------------------------------------------------------------------------
// DyldSharedCache/MappingInfo.hpp
// ----------------------------------------------------------------------------
MappingInfo::Iterator::Iterator() = default;

MappingInfo::Iterator::Iterator(std::unique_ptr<details::MappingInfoIt> impl) :
  impl_(std::move(impl)) {}

MappingInfo::Iterator::Iterator(MappingInfo::Iterator&&) noexcept = default;
MappingInfo::Iterator&
    MappingInfo::Iterator::operator=(MappingInfo::Iterator&&) noexcept = default;

MappingInfo::Iterator::Iterator(const MappingInfo::Iterator& other) :
  impl_(other.impl_ == nullptr ? nullptr :
        std::make_unique<details::MappingInfoIt>(*other.impl_)) {}

MappingInfo::Iterator&
    MappingInfo::Iterator::operator=(const MappingInfo::Iterator& other) {
  if (this == &other) {
    return *this;
  }
  impl_ = other.impl_ == nullptr ? nullptr :
          std::make_unique<details::MappingInfoIt>(*other.impl_);
  cached_.reset();
  return *this;
}

MappingInfo::Iterator::~Iterator() = default;

bool MappingInfo::Iterator::operator<(const MappingInfo::Iterator& rhs) const {
  return impl_ != nullptr && rhs.impl_ != nullptr && impl_->idx < rhs.impl_->idx;
}

std::ptrdiff_t MappingInfo::Iterator::operator-(const Iterator& rhs) const {
  if (impl_ == nullptr || rhs.impl_ == nullptr) {
    return 0;
  }
  return static_cast<std::ptrdiff_t>(impl_->idx) -
         static_cast<std::ptrdiff_t>(rhs.impl_->idx);
}

MappingInfo::Iterator& MappingInfo::Iterator::operator+=(std::ptrdiff_t n) {
  if (impl_ != nullptr) {
    impl_->idx += n;
    cached_.reset();
  }
  return *this;
}

MappingInfo::Iterator& MappingInfo::Iterator::operator-=(std::ptrdiff_t n) {
  return *this += -n;
}

bool operator==(const MappingInfo::Iterator& lhs,
                const MappingInfo::Iterator& rhs) {
  if (lhs.impl_ == nullptr || rhs.impl_ == nullptr) {
    return lhs.impl_ == nullptr && rhs.impl_ == nullptr;
  }
  return lhs.impl_->cache == rhs.impl_->cache && lhs.impl_->idx == rhs.impl_->idx;
}

void MappingInfo::Iterator::load() const {
  if (cached_ != nullptr || impl_ == nullptr || impl_->cache == nullptr) {
    return;
  }
  const mapping_t* mapping = impl_->cache->mapping_at(impl_->idx);
  if (mapping == nullptr) {
    return;
  }
  cached_ = std::make_unique<MappingInfo>(
      std::make_unique<details::MappingInfo>(impl_->cache, *mapping)
  );
}

const MappingInfo& MappingInfo::Iterator::operator*() const {
  load();
  return *cached_;
}

const MappingInfo* MappingInfo::Iterator::operator->() const {
  load();
  return cached_.get();
}

std::unique_ptr<MappingInfo> MappingInfo::Iterator::yield() {
  load();
  return std::move(cached_);
}

MappingInfo::MappingInfo(std::unique_ptr<details::MappingInfo> impl) :
  impl_(std::move(impl)) {}

MappingInfo::~MappingInfo() = default;

uint64_t MappingInfo::address() const {
  return impl_ == nullptr ? 0 : impl_->mapping_.address;
}

uint64_t MappingInfo::size() const {
  return impl_ == nullptr ? 0 : impl_->mapping_.size;
}

uint64_t MappingInfo::file_offset() const {
  return impl_ == nullptr ? 0 : impl_->mapping_.file_offset;
}

uint32_t MappingInfo::max_prot() const {
  return impl_ == nullptr ? 0 : impl_->mapping_.max_prot;
}

uint32_t MappingInfo::init_prot() const {
  return impl_ == nullptr ? 0 : impl_->mapping_.init_prot;
}

// ----------------------------------------------------------------------------
// DyldSharedCache/SubCache.hpp
// ----------------------------------------------------------------------------
SubCache::Iterator::Iterator() = default;

SubCache::Iterator::Iterator(std::unique_ptr<details::SubCacheIt> impl) :
  impl_(std::move(impl)) {}

SubCache::Iterator::Iterator(SubCache::Iterator&&) noexcept = default;
SubCache::Iterator& SubCache::Iterator::operator=(SubCache::Iterator&&) noexcept = default;

SubCache::Iterator::Iterator(const SubCache::Iterator& other) :
  impl_(other.impl_ == nullptr ? nullptr :
        std::make_unique<details::SubCacheIt>(*other.impl_)) {}

SubCache::Iterator& SubCache::Iterator::operator=(const SubCache::Iterator& other) {
  if (this == &other) {
    return *this;
  }
  impl_ = other.impl_ == nullptr ? nullptr :
          std::make_unique<details::SubCacheIt>(*other.impl_);
  cached_.reset();
  return *this;
}

SubCache::Iterator::~Iterator() = default;

bool SubCache::Iterator::operator<(const SubCache::Iterator& rhs) const {
  return impl_ != nullptr && rhs.impl_ != nullptr && impl_->idx < rhs.impl_->idx;
}

std::ptrdiff_t SubCache::Iterator::operator-(const Iterator& rhs) const {
  if (impl_ == nullptr || rhs.impl_ == nullptr) {
    return 0;
  }
  return static_cast<std::ptrdiff_t>(impl_->idx) -
         static_cast<std::ptrdiff_t>(rhs.impl_->idx);
}

SubCache::Iterator& SubCache::Iterator::operator+=(std::ptrdiff_t n) {
  if (impl_ != nullptr) {
    impl_->idx += n;
    cached_.reset();
  }
  return *this;
}

SubCache::Iterator& SubCache::Iterator::operator-=(std::ptrdiff_t n) {
  return *this += -n;
}

bool operator==(const SubCache::Iterator& lhs,
                const SubCache::Iterator& rhs) {
  if (lhs.impl_ == nullptr || rhs.impl_ == nullptr) {
    return lhs.impl_ == nullptr && rhs.impl_ == nullptr;
  }
  return lhs.impl_->cache == rhs.impl_->cache && lhs.impl_->idx == rhs.impl_->idx;
}

void SubCache::Iterator::load() const {
  if (cached_ != nullptr || impl_ == nullptr || impl_->cache == nullptr) {
    return;
  }
  const subcache_t* subcache = impl_->cache->subcache_at(impl_->idx);
  if (subcache == nullptr) {
    return;
  }
  cached_ = std::make_unique<SubCache>(
      std::make_unique<details::SubCache>(impl_->cache, *subcache)
  );
}

const SubCache& SubCache::Iterator::operator*() const {
  load();
  return *cached_;
}

const SubCache* SubCache::Iterator::operator->() const {
  load();
  return cached_.get();
}

std::unique_ptr<SubCache> SubCache::Iterator::yield() {
  load();
  return std::move(cached_);
}

SubCache::SubCache(std::unique_ptr<details::SubCache> impl) :
  impl_(std::move(impl)) {}

SubCache::~SubCache() = default;

sc_uuid_t SubCache::uuid() const {
  return impl_ == nullptr ? sc_uuid_t{} : impl_->subcache_.uuid;
}

uint64_t SubCache::vm_offset() const {
  return impl_ == nullptr ? 0 : impl_->subcache_.vm_offset;
}

std::string SubCache::suffix() const {
  return impl_ == nullptr ? "" : impl_->subcache_.suffix;
}

std::unique_ptr<const DyldSharedCache> SubCache::cache() const {
  if (impl_ == nullptr || impl_->cache_ == nullptr || impl_->subcache_.path.empty()) {
    return nullptr;
  }
  return impl_->cache_->load_cache_from_path(impl_->subcache_.path);
}

}

// NOLINTEND
