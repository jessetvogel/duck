import Lake
open Lake DSL

package Duck {
  dependencies := #[{
    name := `aesop
    src := Source.git "https://github.com/JLimperg/aesop" "5ecb3fb6b70b95e9e227f4e8add80024dadb4e02"
  }]
}
