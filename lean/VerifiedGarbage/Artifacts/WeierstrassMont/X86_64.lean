import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Weierstrass.X86_64.Mont
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnXVerified

/-! # Montgomery products modulo P-521's `p` on x86-64 -/

namespace VG.Artifacts.WeierstrassMont.X86_64

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86_64.Mont VG.Proof.Weierstrass.X86_64.Mont

/-- How both functions start and end. -/
def common : String := "The function zero-extends the offsets, keeps `o` in `rsi` and saves the \
  callee-saved registers it writes in `xmm0`–`xmm5` (`movq`); it writes only `[o]` and its \
  temporary area, the last nine words below byte 4096 of `ws`. It reads `[a]` through \
  `rbx = ws + a` and squares (when `a = b`, a public comparison) or multiplies by `[b]` into its \
  temporary area. As `p = 2⁵²¹ - 1 ≡ -1 (mod 2⁶⁴)`, each reduction's multiplier is a word of the \
  product, and adding `u p` adds `512 u` eight words up. The result `W < 2p`, plus one, is reduced \
  by its bit 521: `W - p` if it is set, else `W`, stored at `o` with `rdi` moved there; the \
  registers come back from `xmm0`–`xmm5`."

def artifacts : List Artifact := [
  { p521p.mulApi with
    target := X86_64.target
    doc := p521p.mulApi.doc (notes := [common, "Montgomery multiplication by columns (product \
      scanning, the accumulator in three registers, `mul`, `[b]` through `rbp = ws + b`; a square \
      computes each product of two different words once and adds it twice)."])
    code := mulFn
    contract := p521p.mulContract X86_64.abi
    verified := p521p_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p521p.mulApi with
    target := X86_64.target
    name := p521p.mulApi.name ++ "_adx"
    doc := p521p.mulApi.doc (notes := [common, "With BMI2 and ADX: the product by rows, each row's \
      products by `mulx` added through two carry chains (`adcx`, `adox`), `[a]` first copied into \
      the temporary area (row `i` reads `a_i` there before it stores its low word over it) and \
      `[b]` through `rbx = ws + b`; a square computes the products of two different words by \
      rows, then doubles them and adds the squares in one pass."])
    code := mulFnX
    contract := p521p.mulContract X86_64.abi
    verified := p521p_mulX_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }
]

end VG.Artifacts.WeierstrassMont.X86_64
