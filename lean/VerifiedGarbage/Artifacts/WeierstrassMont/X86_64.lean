module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Mont
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnXVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFn6Verified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnNVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN6Verified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Impl.Weierstrass.Slots
import VerifiedGarbage.Spec.Ecdsa.Generic

/-! # Montgomery products modulo P-384's and P-521's `p` and `n` on x86-64 -/

@[expose] public section

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

/-- How both P-384 functions run. -/
def common6 : String := "The function zero-extends the offsets and saves the callee-saved registers it \
  writes in `xmm0`–`xmm5` (`movq`); it writes only `[o]` and its temporary area, the last six words \
  below byte 4096 of `ws`. It runs the inline product of the other P-384 functions with its \
  operands read through registers: `[a]` through `rbx = ws + a`, and it squares (when `a = b`, a \
  public comparison), `[o]` through `rsi = ws + o`, or multiplies by `[b]` through `rsi = ws + b`, \
  `o` kept in `xmm6` meanwhile. Each reduction adds `u p` for `u = t₀ (2³² + 1) mod 2⁶⁴`, which \
  makes the low word zero, as `2³⁸⁴ u` less `u (2¹²⁸ + 2⁹⁶ - 2³² + 1)`. The result, below `2p`, \
  is reduced against `p` built in registers: `p` subtracted and added back under the mask of the \
  borrow."

def artifacts6 : List Artifact := [
  { p384p.mulApi with
    target := X86_64.target
    doc := p384p.mulApi.doc (notes := [common6, "Montgomery multiplication by rows of `mul` (operand \
      scanning, the accumulator in eight registers); a square computes each product of two different \
      words once, doubles them and adds the squares, and reduces its low half by six rounds, to which \
      its high half is added."])
    code := mulFn6 false
    contract := p384p.mulContract X86_64.abi
    verified := p384p_mul_verified false
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p384p.mulApi with
    target := X86_64.target
    name := p384p.mulApi.name ++ "_adx"
    doc := p384p.mulApi.doc (notes := [common6, "With BMI2 and ADX: the product by rows, each row's \
      products by `mulx` added through two carry chains (`adcx`, `adox`), the first row's through one, \
      each reduction's `u` by `imul` and its products by `mulx`; a square computes the products of \
      two different words by rows, then doubles them through CF and adds the squares through OF."])
    code := mulFn6 true
    contract := p384p.mulContract X86_64.abi
    verified := p384p_mul_verified true
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }
]

def artifacts : List Artifact := artifacts6 ++ [
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
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p521n.mulApi with
    target := X86_64.target
    doc := p521n.mulApi.doc (notes := ["The function zero-extends the offsets and saves the \
      callee-saved registers it writes in `xmm0`–`xmm5` (`movq`), and the eighty bytes of `ws` from \
      byte 3944 in `xmm6`–`xmm10`, over which it stores `n`; it writes only `[o]` and its temporary \
      area, the last nine words below byte 4096 of `ws`, and restores those bytes. It runs the \
      inline product of the other P-521 functions modulo `n` with its operands read through \
      registers: `[a]` through `rbx = ws + a`, `[b]` through `rbp = ws + b` and `[o]` through \
      `rsi = ws + o`. Montgomery multiplication by columns (product scanning, the accumulator in \
      three registers, `mul`): column `c` adds its products and the reduction's `u_k n_j`, and for \
      `c < 9` computes `u_c = t₀ (-n⁻¹) mod 2⁶⁴`, which clears the low word; the result, below \
      `2n`, is reduced by subtracting `n` and selecting the difference unless it borrowed."])
    code := mulFnN
    contract := p521n.mulContract X86_64.abi
    verified := p521n_mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p384n.mulApi with
    target := X86_64.target
    doc := p384n.mulApi.doc (notes := ["The function zero-extends the offsets and saves the \
      callee-saved registers it writes in `xmm0`–`xmm5` (`movq`), `o` in `xmm6`, and the forty-eight \
      bytes of `ws` from byte 4000 in `xmm7`–`xmm12`, over which it stores `n`; it writes only `[o]` \
      and its temporary area, the last six words below byte 4096 of `ws`, and restores those bytes. \
      It runs the inline product of the other P-384 functions modulo `n` with its operands read \
      through registers: `[a]` through `rbx = ws + a` and `[b]` through `rsi = ws + b`. Montgomery \
      multiplication by rows (operand scanning, `mul`): row `i` adds `a_i b`, computes \
      `u = t₀ (-n⁻¹) mod 2⁶⁴` and adds `u n`, which clears the low word, the accumulator in \
      registers; the result, below `2n`, is reduced by subtracting `n` and selecting the difference \
      unless it borrowed, then stored through `rsi = ws + o`."])
    code := mulFnN6 false
    contract := p384n.mulContract X86_64.abi
    verified := p384n_mul_verified false
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { p384n.mulApi with
    target := X86_64.target
    name := p384n.mulApi.name ++ "_adx"
    doc := p384n.mulApi.doc (notes := ["The function zero-extends the offsets and saves the \
      callee-saved registers it writes in `xmm0`–`xmm5` (`movq`), `o` in `xmm6`, and the forty-eight \
      bytes of `ws` from byte 4000 in `xmm7`–`xmm12`, over which it stores `n`; it writes only `[o]` \
      and its temporary area, the last six words below byte 4096 of `ws`, and restores those bytes. \
      It runs the inline product of the other P-384 functions modulo `n` with its operands read \
      through registers: `[a]` through `rbx = ws + a` and `[b]` through `rsi = ws + b`. With BMI2 \
      and ADX, Montgomery multiplication by rows (operand scanning, `mulx`, the carries through CF \
      and OF): row `i` adds `a_i b`, computes `u = t₀ (-n⁻¹) mod 2⁶⁴` and adds `u n`, which clears \
      the low word, the accumulator in \
      registers; the result, below `2n`, is reduced by subtracting `n` and selecting the difference \
      unless it borrowed, then stored through `rsi = ws + o`."])
    code := mulFnN6 true
    contract := p384n.mulContract X86_64.abi
    verified := p384n_mul_verified true
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }
]

end VG.Artifacts.WeierstrassMont.X86_64
