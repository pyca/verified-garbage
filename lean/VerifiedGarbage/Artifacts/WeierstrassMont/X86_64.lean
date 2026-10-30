module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFn6Verified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnNVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN6Verified
public import VerifiedGarbage.Proof.Framework.Registration

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

def artifacts6 : List Artifact := [
  p384p.mulApi.artifact X86_64.target {
    code := mulFn6 false
    verified := p384p_mul_verified false },
  p384p.mulApi.artifact X86_64.target {
    suffix := "_adx"
    code := mulFn6 true
    verified := p384p_mul_verified true
    features := ["bmi2", "adx"] }
]

def artifacts : List Artifact := artifacts6 ++ [
  p521p.mulApi.artifact X86_64.target {
    code := mulFn
    verified := p521p_mul_verified },
  p521p.mulApi.artifact X86_64.target {
    suffix := "_adx"
    code := mulFnX
    verified := p521p_mulX_verified
    features := ["bmi2", "adx"] },
  p521n.mulApi.artifact X86_64.target {
    code := mulFnN
    verified := p521n_mul_verified },
  p384n.mulApi.artifact X86_64.target {
    code := mulFnN6 false
    verified := p384n_mul_verified false },
  p384n.mulApi.artifact X86_64.target {
    suffix := "_adx"
    code := mulFnN6 true
    verified := p384n_mul_verified true
    features := ["bmi2", "adx"] }
]

end VG.Artifacts.WeierstrassMont.X86_64
