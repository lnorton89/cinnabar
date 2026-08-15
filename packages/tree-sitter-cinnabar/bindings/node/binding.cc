#include <napi.h>

typedef struct TSLanguage TSLanguage;

extern "C" const TSLanguage *tree_sitter_cinnabar(void);

// "tree-sitter" "language" version
Napi::Object Init(Napi::Env env, Napi::Object exports) {
  exports["name"] = Napi::String::New(env, "cinnabar");
  auto language = Napi::External<TSLanguage>::New(env, const_cast<TSLanguage *>(tree_sitter_cinnabar()));
  language.TypeTag(&exports.Env().Global());
  exports["language"] = language;
  return exports;
}

NODE_API_MODULE(tree_sitter_cinnabar_binding, Init)
