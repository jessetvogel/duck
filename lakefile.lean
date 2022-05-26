import Lake
open Lake DSL

package Duck {
  dependencies := #[{
    name := `aesop
    src := Source.git "https://github.com/JLimperg/aesop" "6121cc4764ccb26ee0c2d4aaa720618f03338f8a"
  }]
}
