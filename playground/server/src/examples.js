// The example corpus, as short programs rather than as a tour.
//
// Each one is chosen because it shows something the compiler will say
// something interesting about — a linear handle consumed on one path and
// not another, a layout worth looking at, an exhaustive match. The
// repository's own fixtures are the canonical tour and are much longer;
// these are sized for a first minute in an editor.

export const EXAMPLES = [
  {
    id: "hello",
    title: "Hello",
    blurb: "The smallest program that compiles, links, and exits 0.",
    source: `pub fun main() I64
  return 0
end
`,
  },
  {
    id: "struct-layout",
    title: "A struct and its layout",
    blurb: "Declare a product type, then read the ABI size and field offsets the compiler computed for it.",
    source: `pub type Point
  pub x: I64
  pub y: I64
end

pub fun main() I64
  val origin = Point(x: 0, y: 0)
  return origin.x
end
`,
  },
  {
    id: "exhaustive-match",
    title: "Match is exhaustive",
    blurb: "Every variant must be named. Delete an arm and the compiler says which one is missing.",
    source: `pub type Shade
  Dim
  Bright(I64)
end

fun level(shade: Shade) I64
  match shade
    Dim => return 0
    Bright(value) => return value
  end
end

pub fun main() I64
  return level(Bright(1))
end
`,
  },
  {
    id: "casing-is-grammar",
    title: "Casing is grammar",
    blurb: "A mis-cased name is a lexical error, not a style opinion. Rename `Total` to `total` to compile it.",
    source: `pub fun main() I64
  val Total = 1
  return Total
end
`,
  },
  {
    id: "immutable-binding",
    title: "val is immutable",
    blurb: "Assignment needs `var`. This one is rejected; change `val` to `var`.",
    source: `pub fun main() I64
  val count = 0
  count = 1
  return count
end
`,
  },
  {
    id: "division-is-fallible",
    title: "Division returns a Result",
    blurb: "`/` and `%` can fail, so their result must be handled — there is no silent trap.",
    source: `fun halve(value: I64) Result(I64, DivError)
  return value / 2
end

pub fun main() I64
  match halve(10)
    Ok(value) => return value
    Err(error) => return 1
  end
end
`,
  },
];
