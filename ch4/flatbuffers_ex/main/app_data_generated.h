// automatically generated by the FlatBuffers compiler, do not modify


#ifndef FLATBUFFERS_GENERATED_APPDATA_APP_H_
#define FLATBUFFERS_GENERATED_APPDATA_APP_H_

#include "flatbuffers/flatbuffers.h"

// Ensure the included flatbuffers.h is the same version as when this file was
// generated, otherwise it may not be compatible.
static_assert(FLATBUFFERS_VERSION_MAJOR == 22 &&
              FLATBUFFERS_VERSION_MINOR == 10 &&
              FLATBUFFERS_VERSION_REVISION == 26,
             "Non-compatible flatbuffers version included");

namespace app {

struct ReadingFb;
struct ReadingFbBuilder;
struct ReadingFbT;

struct LightSensorFb;
struct LightSensorFbBuilder;
struct LightSensorFbT;

struct ReadingFbT : public flatbuffers::NativeTable {
  typedef ReadingFb TableType;
  uint32_t timestamp = 0;
  uint16_t light = 0;
};

struct ReadingFb FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef ReadingFbT NativeTableType;
  typedef ReadingFbBuilder Builder;
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_TIMESTAMP = 4,
    VT_LIGHT = 6
  };
  uint32_t timestamp() const {
    return GetField<uint32_t>(VT_TIMESTAMP, 0);
  }
  uint16_t light() const {
    return GetField<uint16_t>(VT_LIGHT, 0);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyField<uint32_t>(verifier, VT_TIMESTAMP, 4) &&
           VerifyField<uint16_t>(verifier, VT_LIGHT, 2) &&
           verifier.EndTable();
  }
  ReadingFbT *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(ReadingFbT *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<ReadingFb> Pack(flatbuffers::FlatBufferBuilder &_fbb, const ReadingFbT* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct ReadingFbBuilder {
  typedef ReadingFb Table;
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_timestamp(uint32_t timestamp) {
    fbb_.AddElement<uint32_t>(ReadingFb::VT_TIMESTAMP, timestamp, 0);
  }
  void add_light(uint16_t light) {
    fbb_.AddElement<uint16_t>(ReadingFb::VT_LIGHT, light, 0);
  }
  explicit ReadingFbBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  flatbuffers::Offset<ReadingFb> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<ReadingFb>(end);
    return o;
  }
};

inline flatbuffers::Offset<ReadingFb> CreateReadingFb(
    flatbuffers::FlatBufferBuilder &_fbb,
    uint32_t timestamp = 0,
    uint16_t light = 0) {
  ReadingFbBuilder builder_(_fbb);
  builder_.add_timestamp(timestamp);
  builder_.add_light(light);
  return builder_.Finish();
}

flatbuffers::Offset<ReadingFb> CreateReadingFb(flatbuffers::FlatBufferBuilder &_fbb, const ReadingFbT *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);

struct LightSensorFbT : public flatbuffers::NativeTable {
  typedef LightSensorFb TableType;
  std::string location{};
  std::vector<std::unique_ptr<app::ReadingFbT>> readings{};
  LightSensorFbT() = default;
  LightSensorFbT(const LightSensorFbT &o);
  LightSensorFbT(LightSensorFbT&&) FLATBUFFERS_NOEXCEPT = default;
  LightSensorFbT &operator=(LightSensorFbT o) FLATBUFFERS_NOEXCEPT;
};

struct LightSensorFb FLATBUFFERS_FINAL_CLASS : private flatbuffers::Table {
  typedef LightSensorFbT NativeTableType;
  typedef LightSensorFbBuilder Builder;
  enum FlatBuffersVTableOffset FLATBUFFERS_VTABLE_UNDERLYING_TYPE {
    VT_LOCATION = 4,
    VT_READINGS = 6
  };
  const flatbuffers::String *location() const {
    return GetPointer<const flatbuffers::String *>(VT_LOCATION);
  }
  const flatbuffers::Vector<flatbuffers::Offset<app::ReadingFb>> *readings() const {
    return GetPointer<const flatbuffers::Vector<flatbuffers::Offset<app::ReadingFb>> *>(VT_READINGS);
  }
  bool Verify(flatbuffers::Verifier &verifier) const {
    return VerifyTableStart(verifier) &&
           VerifyOffset(verifier, VT_LOCATION) &&
           verifier.VerifyString(location()) &&
           VerifyOffset(verifier, VT_READINGS) &&
           verifier.VerifyVector(readings()) &&
           verifier.VerifyVectorOfTables(readings()) &&
           verifier.EndTable();
  }
  LightSensorFbT *UnPack(const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  void UnPackTo(LightSensorFbT *_o, const flatbuffers::resolver_function_t *_resolver = nullptr) const;
  static flatbuffers::Offset<LightSensorFb> Pack(flatbuffers::FlatBufferBuilder &_fbb, const LightSensorFbT* _o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);
};

struct LightSensorFbBuilder {
  typedef LightSensorFb Table;
  flatbuffers::FlatBufferBuilder &fbb_;
  flatbuffers::uoffset_t start_;
  void add_location(flatbuffers::Offset<flatbuffers::String> location) {
    fbb_.AddOffset(LightSensorFb::VT_LOCATION, location);
  }
  void add_readings(flatbuffers::Offset<flatbuffers::Vector<flatbuffers::Offset<app::ReadingFb>>> readings) {
    fbb_.AddOffset(LightSensorFb::VT_READINGS, readings);
  }
  explicit LightSensorFbBuilder(flatbuffers::FlatBufferBuilder &_fbb)
        : fbb_(_fbb) {
    start_ = fbb_.StartTable();
  }
  flatbuffers::Offset<LightSensorFb> Finish() {
    const auto end = fbb_.EndTable(start_);
    auto o = flatbuffers::Offset<LightSensorFb>(end);
    return o;
  }
};

inline flatbuffers::Offset<LightSensorFb> CreateLightSensorFb(
    flatbuffers::FlatBufferBuilder &_fbb,
    flatbuffers::Offset<flatbuffers::String> location = 0,
    flatbuffers::Offset<flatbuffers::Vector<flatbuffers::Offset<app::ReadingFb>>> readings = 0) {
  LightSensorFbBuilder builder_(_fbb);
  builder_.add_readings(readings);
  builder_.add_location(location);
  return builder_.Finish();
}

inline flatbuffers::Offset<LightSensorFb> CreateLightSensorFbDirect(
    flatbuffers::FlatBufferBuilder &_fbb,
    const char *location = nullptr,
    const std::vector<flatbuffers::Offset<app::ReadingFb>> *readings = nullptr) {
  auto location__ = location ? _fbb.CreateString(location) : 0;
  auto readings__ = readings ? _fbb.CreateVector<flatbuffers::Offset<app::ReadingFb>>(*readings) : 0;
  return app::CreateLightSensorFb(
      _fbb,
      location__,
      readings__);
}

flatbuffers::Offset<LightSensorFb> CreateLightSensorFb(flatbuffers::FlatBufferBuilder &_fbb, const LightSensorFbT *_o, const flatbuffers::rehasher_function_t *_rehasher = nullptr);

inline ReadingFbT *ReadingFb::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = std::unique_ptr<ReadingFbT>(new ReadingFbT());
  UnPackTo(_o.get(), _resolver);
  return _o.release();
}

inline void ReadingFb::UnPackTo(ReadingFbT *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = timestamp(); _o->timestamp = _e; }
  { auto _e = light(); _o->light = _e; }
}

inline flatbuffers::Offset<ReadingFb> ReadingFb::Pack(flatbuffers::FlatBufferBuilder &_fbb, const ReadingFbT* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateReadingFb(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<ReadingFb> CreateReadingFb(flatbuffers::FlatBufferBuilder &_fbb, const ReadingFbT *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const ReadingFbT* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _timestamp = _o->timestamp;
  auto _light = _o->light;
  return app::CreateReadingFb(
      _fbb,
      _timestamp,
      _light);
}

inline LightSensorFbT::LightSensorFbT(const LightSensorFbT &o)
      : location(o.location) {
  readings.reserve(o.readings.size());
  for (const auto &readings_ : o.readings) { readings.emplace_back((readings_) ? new app::ReadingFbT(*readings_) : nullptr); }
}

inline LightSensorFbT &LightSensorFbT::operator=(LightSensorFbT o) FLATBUFFERS_NOEXCEPT {
  std::swap(location, o.location);
  std::swap(readings, o.readings);
  return *this;
}

inline LightSensorFbT *LightSensorFb::UnPack(const flatbuffers::resolver_function_t *_resolver) const {
  auto _o = std::unique_ptr<LightSensorFbT>(new LightSensorFbT());
  UnPackTo(_o.get(), _resolver);
  return _o.release();
}

inline void LightSensorFb::UnPackTo(LightSensorFbT *_o, const flatbuffers::resolver_function_t *_resolver) const {
  (void)_o;
  (void)_resolver;
  { auto _e = location(); if (_e) _o->location = _e->str(); }
  { auto _e = readings(); if (_e) { _o->readings.resize(_e->size()); for (flatbuffers::uoffset_t _i = 0; _i < _e->size(); _i++) { if(_o->readings[_i]) { _e->Get(_i)->UnPackTo(_o->readings[_i].get(), _resolver); } else { _o->readings[_i] = std::unique_ptr<app::ReadingFbT>(_e->Get(_i)->UnPack(_resolver)); }; } } else { _o->readings.resize(0); } }
}

inline flatbuffers::Offset<LightSensorFb> LightSensorFb::Pack(flatbuffers::FlatBufferBuilder &_fbb, const LightSensorFbT* _o, const flatbuffers::rehasher_function_t *_rehasher) {
  return CreateLightSensorFb(_fbb, _o, _rehasher);
}

inline flatbuffers::Offset<LightSensorFb> CreateLightSensorFb(flatbuffers::FlatBufferBuilder &_fbb, const LightSensorFbT *_o, const flatbuffers::rehasher_function_t *_rehasher) {
  (void)_rehasher;
  (void)_o;
  struct _VectorArgs { flatbuffers::FlatBufferBuilder *__fbb; const LightSensorFbT* __o; const flatbuffers::rehasher_function_t *__rehasher; } _va = { &_fbb, _o, _rehasher}; (void)_va;
  auto _location = _o->location.empty() ? 0 : _fbb.CreateString(_o->location);
  auto _readings = _o->readings.size() ? _fbb.CreateVector<flatbuffers::Offset<app::ReadingFb>> (_o->readings.size(), [](size_t i, _VectorArgs *__va) { return CreateReadingFb(*__va->__fbb, __va->__o->readings[i].get(), __va->__rehasher); }, &_va ) : 0;
  return app::CreateLightSensorFb(
      _fbb,
      _location,
      _readings);
}

inline const app::LightSensorFb *GetLightSensorFb(const void *buf) {
  return flatbuffers::GetRoot<app::LightSensorFb>(buf);
}

inline const app::LightSensorFb *GetSizePrefixedLightSensorFb(const void *buf) {
  return flatbuffers::GetSizePrefixedRoot<app::LightSensorFb>(buf);
}

inline bool VerifyLightSensorFbBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifyBuffer<app::LightSensorFb>(nullptr);
}

inline bool VerifySizePrefixedLightSensorFbBuffer(
    flatbuffers::Verifier &verifier) {
  return verifier.VerifySizePrefixedBuffer<app::LightSensorFb>(nullptr);
}

inline void FinishLightSensorFbBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<app::LightSensorFb> root) {
  fbb.Finish(root);
}

inline void FinishSizePrefixedLightSensorFbBuffer(
    flatbuffers::FlatBufferBuilder &fbb,
    flatbuffers::Offset<app::LightSensorFb> root) {
  fbb.FinishSizePrefixed(root);
}

inline std::unique_ptr<app::LightSensorFbT> UnPackLightSensorFb(
    const void *buf,
    const flatbuffers::resolver_function_t *res = nullptr) {
  return std::unique_ptr<app::LightSensorFbT>(GetLightSensorFb(buf)->UnPack(res));
}

inline std::unique_ptr<app::LightSensorFbT> UnPackSizePrefixedLightSensorFb(
    const void *buf,
    const flatbuffers::resolver_function_t *res = nullptr) {
  return std::unique_ptr<app::LightSensorFbT>(GetSizePrefixedLightSensorFb(buf)->UnPack(res));
}

}  // namespace app

#endif  // FLATBUFFERS_GENERATED_APPDATA_APP_H_