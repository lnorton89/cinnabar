{
  "targets": [
    {
      "target_name": "tree_sitter_cinnabar_binding",
      "include_dirs": ["src"],
      "sources": ["bindings/node/binding.cc", "src/parser.c", "src/scanner.c"],
      "cflags_c": ["-std=c11"]
    }
  ]
}
