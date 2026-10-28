module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Init
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Loop
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Correct
import VerifiedGarbage.Proof.Rsa.Divstep.InvCorrect
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Encoding
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.Ring.Abs

/-! # The batched inverse at a run-time width

`body_ok`: `[1] = gcd p x` and `[3]` the inverse of `x` modulo `p` where it exists, `w` words each,
for the virtual modulus `p` of `[8]` and `x` at `[0]` (`InvBatch.body_ok_proof`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.Divstep (oddInput)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- What the inverse writes: the header from the window on, and arrays 0 to 14. -/
def bodyWrites (len : Nat) : List (Nat × Nat) := [(win, 88), (rv (kw len) (a 0), 15 * (8 * nw len + 8))]

theorem body_ok {s : State} (h : RtWs L s B Z len N) (room : 16 ≤ N) (hn2 : 2 ≤ nw len)
    (he : nw len % 2 = 0) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 8)) (nw len) = m) (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len) = x)
    (odd : m % 2 = 1) :
    WP isa (body L) s fun z =>
      Bx L z B Z len N ∧
      val32 z.mem B (rv (kw len) (a 1)) (kw len) = Nat.gcd (virtualMod m) x ∧
      (virtualMod m : Int) ∣ (val32 z.mem B (rv (kw len) (a 3)) (kw len) : Int) * x - (Nat.gcd (virtualMod m) x : Int) ∧
      val32 z.mem B (rv (kw len) (a 3)) (kw len) < virtualMod m ∧
      Keeps wordClob s z ∧ Unch B (bodyWrites len) s.mem z.mem := by
  have hn := h.ws.workspace.nowrap
  have hw := kw_bound h.lenLe
  have ke := kw_eq len
  have e16 : win = 16 := rfl
  have e48 : signSlot = 48 := rfl
  let p := virtualMod m
  have po : p % 2 = 1 := virtualMod_odd odd
  have pl : 1 < p := by simp only [p, virtualMod]; split <;> omega
  have mp : m < 2 ^ (32 * nw len) := hm ▸ val32_lt _ _ _ _
  have pc : p < 2 ^ (32 * nw len) := by
    have four : 4 ≤ 2 ^ (32 * nw len) := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ 32 * nw len by omega)
    simp only [p, virtualMod]; split <;> omega
  have xc : x < 2 ^ (32 * nw len) := hx ▸ val32_lt _ _ _ _
  unfold body
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (init_ok h room hn2 hm hx odd) fun s₁ ⟨iv, H₁, I₁, inv, C₁, K₁, O₁⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok H₁ he I₁ C₁ po pl inv pc xc) fun s₂ ⟨H₂, I₂, _, K₂, O₂⟩ => ?_)
  have hf16 := H₂.fits16
  have r0 := rv_a len 0; have r1 := rv_a len 1; have r2 := rv_a len 2; have r3 := rv_a len 3
  have r4 := rv_a len 4; have r6 := rv_a len 6; have r11 := rv_a len 11; have r12 := rv_a len 12
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  let st := Divstep.W32.invRun 30 p iv (oddInput p x) (3 * (nw len + 1))
  have result := VG.Proof.Rsa.Divstep.invRun_result (iv := iv) po pl inv pc xc
  change st.f.natAbs = Nat.gcd p x ∧
    (p : Int) ∣ (VG.Proof.Rsa.Divstep.corrected p st (3 * (nw len + 1))).toNat * (x : Int) - (Nat.gcd p x : Int) ∧
    (VG.Proof.Rsa.Divstep.corrected p st (3 * (nw len + 1))).toNat < p at result
  have bounds := VG.Proof.Rsa.Divstep.invRun_bounds (inv := iv) (cap := p + x) po pl inv (by omega)
    (show oddInput p x ≤ p + x by unfold oddInput; split <;> omega) (3 * (nw len + 1))
  have fb : |st.f| < (2 : Int) ^ (32 * nw len) := by
    have gBound : Nat.gcd p x < 2 ^ (32 * nw len) := (Nat.gcd_le_left x (by omega : 0 < p)).trans_lt pc
    have : st.f.natAbs < 2 ^ (32 * nw len) := result.1 ▸ gBound
    have cast : (st.f.natAbs : Int) < (2 : Int) ^ (32 * nw len) := by exact_mod_cast this
    simpa only [Int.natCast_natAbs] using cast
  have a0 := bounds.2.2.2.2.1
  have ap := bounds.2.2.2.2.2.1
  let a₀ := st.a.toNat
  have sa : st.a = (a₀ : Int) := (Int.toNat_of_nonneg a0).symm
  have small : a₀ < p := by exact_mod_cast (sa ▸ ap)
  have ha : val32 s₂.mem B (rv (kw len) (a 6)) (nw len) = a₀ := by exact_mod_cast I₂.ca.trans sa
  have sign := VG.Proof.Rsa.X86.GcdBatch.encoding_sign I₂.f fb
  -- The sign.
  refine WP.seq (WP.mono (normalize_ok H₂ I₂.modulus ha I₂.aTop small sign)
    fun s₃ ⟨H₃, V₃, T₃, K₃, U₃⟩ => ?_)
  have mod3 : val32 s₃.mem B (rv (kw len) mo) (nw len) = p := by
    rw [Outs.val32 U₃ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega), I₂.modulus]
  -- The scale: `6 (n + 1)` doublings.
  unfold doublings
  refine WP.seq (nBytes_ok H₃.ws.ws.workspace H₃.slots H₃.halfZ (by omega) (e := 1) (by decide)
    fun s₄ K₄ m₄ c₄ => ?_)
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₅ V₅ => ?_
  refine wp_movS rfl fun s₆ V₆ _ => wp_addS rfl fun s₇ V₇ _ => wp_addS rfl fun s₈ V₈ _ => WP.block_nil ?_
  have K₈ : Keeps [.eax, .esi] s₃ s₈ :=
    ((((K₄.mono (by decide)).trans (V₅.keeps.mono (by decide))).trans (V₆.keeps.mono (by decide))).trans
      (V₇.keeps.mono (by decide))).trans (V₈.keeps.mono (by decide))
  have m₈ : s₈.mem = s₃.mem := by rw [V₈.mem, V₇.mem, V₆.mem, V₅.mem, m₄]
  have H₈ : Bx L s₈ B Z len N := H₃.keep K₈ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₈]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have cnt : s₈.gpr .esi = BitVec.ofNat 32 (6 * (nw len + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [V₈.gpr, V₇.gpr, V₇.other .eax (by decide), V₆.gpr]
    have e₄ : (s₄.gpr .esi).toNat = 4 * (nw len + 1) := by rw [c₄]; omega
    have e₅ : (s₅.gpr .esi).toNat = 2 * (nw len + 1) := by
      rw [V₅.gpr, BitVec.toNat_ushiftRight, e₄, Nat.shiftRight_eq_div_pow]; omega
    have e₆ : s₆.gpr .esi = s₅.gpr .esi := V₆.other _ (by decide)
    rw [e₆]
    simp only [BitVec.toNat_add, e₅, BitVec.toNat_ofNat]
    omega
  refine WP.seq (WP.mono (doubleLoop_ok H₈ (by rw [m₈]; exact mod3) (by rw [m₈]; exact V₃) (by rw [m₈]; exact T₃)
    (by omega) (normal_range st.f (by omega) small) (by omega) (by omega) cnt)
    fun s₉ ⟨H₉, V₉, T₉, M₉, C₉, K₉, U₉⟩ => ?_)
  have f9 : (val32 s₉.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      st.f % 2 ^ (32 * (nw len + 1)) := by
    rw [Outs.val32 U₉ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega), m₈, Outs.val32 U₃ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)]
    exact I₂.f
  -- The outputs.
  refine WP.mono (finish_ok H₉ fb (VG.Proof.Rsa.X86.GcdBatch.encoding_low f9)
    (VG.Proof.Rsa.X86.GcdBatch.encoding_sign f9 fb) V₉) fun z ⟨Hz, G, A, Kz, Uz⟩ => ?_
  rw [correction_eq small sa] at A
  refine ⟨Hz, G.trans result.1, by rw [A]; exact result.2.1, A ▸ result.2.2, ?_, ?_⟩
  · exact ((((K₁.trans K₂).trans K₃).trans (K₈.mono (by decide))).trans K₉).trans Kz
  · intro y hy
    have h1 := hy (win, 88) (by simp [bodyWrites])
    have h2 := hy (rv (kw len) (a 0), 15 * (8 * nw len + 8)) (by simp [bodyWrites])
    rw [Uz y (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega), U₉ y (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega), m₈, U₃ y (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega), O₂ y (by
      intro r hr
      simp only [countedWrites, updateWrites, rowWrites, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | (rfl | rfl | rfl) | rfl <;> simp only <;> omega), O₁ y (by
      intro r hr; simp only [initWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega)]

end VG.Proof.Rsa.X86.InvBatchRt
