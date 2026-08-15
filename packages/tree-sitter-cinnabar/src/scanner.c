// Newline recognition for Cinnabar.
//
// Cinnabar has no semicolons: a statement ends at the end of its line. But
// a parameter list, an argument list, or an array literal may be spread
// across lines, and a newline inside one of those is continuation, not a
// terminator. That distinction is not expressible in grammar rules, so it
// lives here: the scanner tracks how deep it is inside (), [] and emits a
// newline token only at depth zero.
//
// It also swallows comments while looking ahead, because a line that ends
// in a trailing comment still ends, and a block comment spanning lines
// inside brackets must not manufacture a terminator.

#include "tree_sitter/parser.h"

#include <stdlib.h>
#include <string.h>

enum TokenType {
  NEWLINE,
  ARM_START,
  ERROR_SENTINEL,
};

// The scanner keeps no state. It is only ever invoked where the grammar
// permits an external token, which means it never sees most of a program's
// brackets — so any depth it tried to track would drift. Continuation
// inside brackets is handled instead by the grammar listing the newline as
// an extra, which applies exactly where no terminator is permitted.
typedef struct {
  char unused;
} Scanner;

void *tree_sitter_cinnabar_external_scanner_create(void) {
  Scanner *scanner = calloc(1, sizeof(Scanner));
  return scanner;
}

void tree_sitter_cinnabar_external_scanner_destroy(void *payload) {
  free((Scanner *)payload);
}

unsigned tree_sitter_cinnabar_external_scanner_serialize(void *payload, char *buffer) {
  (void)payload;
  (void)buffer;
  return 0;
}

void tree_sitter_cinnabar_external_scanner_deserialize(void *payload, const char *buffer, unsigned length) {
  (void)payload;
  (void)buffer;
  (void)length;
}

static void skip(TSLexer *lexer) { lexer->advance(lexer, true); }

// Consumes a comment that has already been recognized by its leading '#'.
// Returns true when the comment ran to the end of the line, which is what
// tells the caller a line terminator may still follow.
static bool skip_comment(TSLexer *lexer) {
  skip(lexer); // '#'
  bool documentation = lexer->lookahead == '!';
  if (documentation) {
    skip(lexer);
  }
  if (lexer->lookahead == '|') {
    // Block comment: runs to '|#' and may span lines. Cinnabar block
    // comments do not nest, so the first terminator closes it.
    skip(lexer);
    while (!lexer->eof(lexer)) {
      if (lexer->lookahead == '|') {
        skip(lexer);
        if (lexer->lookahead == '#') {
          skip(lexer);
          return false;
        }
        continue;
      }
      skip(lexer);
    }
    return false;
  }
  while (!lexer->eof(lexer) && lexer->lookahead != '\n') {
    skip(lexer);
  }
  return true;
}

// True when the rest of the current logical line holds a `=>` outside any
// bracket. That is the only thing distinguishing the next match arm from
// another statement of the arm body above it: a match arm's block has no
// closing keyword, so the parser has to be told, before reading the
// pattern, that a pattern is what is coming.
static bool line_holds_arrow(TSLexer *lexer) {
  unsigned depth = 0;
  while (!lexer->eof(lexer)) {
    int32_t character = lexer->lookahead;
    if (character == '\n') {
      return false;
    }
    if (character == '#') {
      if (skip_comment(lexer)) {
        return false;
      }
      continue;
    }
    if (character == '(' || character == '[') {
      depth += 1;
    } else if (character == ')' || character == ']') {
      if (depth > 0) {
        depth -= 1;
      }
    } else if (character == '"') {
      // A `=>` inside a string literal is text, not an arm separator.
      skip(lexer);
      while (!lexer->eof(lexer) && lexer->lookahead != '"' && lexer->lookahead != '\n') {
        if (lexer->lookahead == '\\') {
          skip(lexer);
          if (lexer->eof(lexer)) {
            return false;
          }
        }
        skip(lexer);
      }
    } else if (character == '=' && depth == 0) {
      skip(lexer);
      if (lexer->lookahead == '>') {
        return true;
      }
      continue;
    }
    skip(lexer);
  }
  return false;
}

bool tree_sitter_cinnabar_external_scanner_scan(void *payload, TSLexer *lexer, const bool *valid_symbols) {
  (void)payload;

  if (valid_symbols[ERROR_SENTINEL]) {
    // In error recovery tree-sitter marks every external token valid.
    // Emitting a terminator into a parse that is already broken would only
    // make the recovery worse, so decline.
    return false;
  }

  bool saw_newline = false;
  while (!lexer->eof(lexer)) {
    if (lexer->lookahead == '\n') {
      saw_newline = true;
      skip(lexer);
      continue;
    }
    if (lexer->lookahead == ' ' || lexer->lookahead == '\t' || lexer->lookahead == '\r') {
      skip(lexer);
      continue;
    }
    if (lexer->lookahead == '#') {
      // A trailing comment does not stop the line from ending, and a block
      // comment that spans lines does not by itself end one either.
      if (skip_comment(lexer)) {
        continue;
      }
      continue;
    }
    break;
  }

  // A zero-width marker: `mark_end` is set before looking ahead, so the
  // token occupies no source and the pattern that follows is still there
  // to be parsed.
  if (valid_symbols[ARM_START]) {
    lexer->mark_end(lexer);
    if (line_holds_arrow(lexer)) {
      lexer->result_symbol = ARM_START;
      return true;
    }
    if (!valid_symbols[NEWLINE]) {
      return false;
    }
    // Looking ahead moved the lexer past the pattern; the newline this call
    // would otherwise report was already consumed above, and `mark_end`
    // pinned the token's extent before any of that. Reporting it here keeps
    // the terminator the block still needs.
    if (saw_newline) {
      lexer->result_symbol = NEWLINE;
      return true;
    }
    return false;
  }

  if (!valid_symbols[NEWLINE]) {
    return false;
  }
  if (!saw_newline && !lexer->eof(lexer)) {
    return false;
  }
  lexer->result_symbol = NEWLINE;
  return true;
}
