module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGDHash
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGKs
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Decryption: the blocks after the last group, as a masked group

`ksBatchGD_ok`: `StitchZH.ksBatchGD k` puts the mask of the last register's
blocks in `r10` (`remMaskG_ok`), encrypts the counters `c …` in the lanes of
`k` registers while it hashes the `r` ciphertext blocks at `rdx` between the
rounds (`gD_ok`), and adds the blocks to the keystream and stores them
(`xorG_ok`): the blocks decrypted in place, and `Y` their `GHASH` lanes,
reduced and added (`yLanes`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH (remMaskG xorG gD ksBatchGD)
open VG.Proof.Gcm.X86_64.StitchZ (aregs_ok gRegs gRegs_ok)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Proof.Gcm.X86_64.Stitch (SPre nr kp pp cb dR pR cR ciph sch in_rdwr)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq)
open VG.Spec.Gcm (Block blockAt inc32)

theorem remMaskG_noCalls : remMaskG.noCalls = true := rfl
theorem remMaskG_keeps : remMaskG.all Instr.keepsH = true := rfl

/-- The `r` ciphertext blocks at `A` (`rdx`) as a group of `k` registers:
their counters `c …` encrypted while the blocks are hashed between the
rounds with the powers at `W` (`rax`), from `Y` in lane 0 of `xmm2`, and the
blocks decrypted in place. -/
theorem ksBatchGD_ok {s₀ : State} (hp : SPre s₀) {k r : Nat} (hk4 : k ≤ 4) (hr1 : 1 ≤ r) (hr15 : r ≤ 15)
    (hrk : r ≤ 4 * k) (hkr : 4 * k < r + 4) {A W : Addr} {T : Nat → BitVec 128} {y : Block} {c : Nat}
    {s : State}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hA : s.gpr .rdx = A) (hW : s.gpr .rax = W)
    (hT : ∀ n < r, s.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinA : InRegions s.wr A (16 * r)) (hinW : InRegions (s.rd ++ s.wr) W (16 * r))
    (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) (h2 : ∀ l < 4, s.zlane .xmm2 l = if l = 0 then y else 0)
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask) (hinc : ∀ l < 4, s.zlane .xmm15 l = four)
    (hrdi : s.gpr .rdi = kp s₀) (hrsi : s.gpr .rsi = s₀.gpr .rsi)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hfr : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s.mem)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (ksBatchGD k) s fun s' =>
      (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
        blockAt s.mem (A + BitVec.ofNat 64 (16 * n)) ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
      Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
      s'.zlane .xmm2 0 = yLanes (fun n => blockAt s.mem (A + BitVec.ofNat 64 (16 * n))) T y r ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm14] ++ gRegs : List XReg) → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
  have hwp := hp.wrap_p
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hnd' : (aregs.take k).Nodup := hnd.sublist (List.take_sublist _ _)
  have hx' : ∀ r ∈ aregs.take k, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := fun r hr => hx r (List.mem_of_mem_take hr)
  have h13' : .xmm13 ∉ aregs.take k := fun h => h13 (List.mem_of_mem_take h)
  have hlen : (aregs.take k).length = k := by simp [aregs]; omega
  have hk1 : 1 ≤ k := by omega
  let c' := (r - 1) % 4 + 1
  have hc : 4 * (k - 1) + c' = r := by omega
  obtain ⟨mq, mb⟩ := maskG_ok c' (by omega) (by omega)
  have hK : Keys (nr s₀) (sch s₀) s := keys_of hp hrdi hrd hwr hfr
  -- The mask.
  refine WP.seq (WP.mono (WP.hkeepCode remMaskG_noCalls remMaskG_keeps (remMaskG_ok s hr1 (by omega) h9))
    fun t ⟨⟨a₀, g₀, l₀, m₀, rd₀, wr₀⟩, hh₀⟩ => ?_)
  have hK₀ : Keys (nr s₀) (sch s₀) t :=
    keys_of hp (by rw [g₀ _ (by decide)]; exact hrdi) (by rw [rd₀]; exact hrd) (by rw [wr₀]; exact hwr)
      (by rw [m₀]; exact hfr)
  have hCache₀ := hCache.keep hh₀ hK₀
  -- The counters.
  refine WP.seq (WP.mono (WP.hkeep (ctrsZ_keeps _ _ _ _) (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide)
    (aregs.take k) t (cb s₀) c hnd' hx' (fun l hl => by rw [l₀]; exact hctr l hl)
    (fun l hl => by rw [l₀]; exact hmsk l hl) (fun l hl => by rw [l₀]; exact hinc l hl)))
    fun s₁ ⟨⟨e₁, c₁, f₁⟩, hh₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys hK₀ f₁
  have hCache₁ := hCache₀.keep hh₁ hK₁
  -- The GHASH environment of the rounds.
  let X' : Nat → Block := fun n => blockAt s.mem (A + BitVec.ofNat 64 (16 * n))
  let T' : Nat → BitVec 128 := fun n => if n < r then T n else 0
  have kz₁ : ∀ x, x ≠ .xmm14 → x ∉ aregs.take k → ∀ l < 4, s₁.zlane x l = s.zlane x l := fun x h14 hx l hl => by
    rw [f₁.zlane x (by simp only [List.mem_cons, not_or]; exact ⟨h14, hx⟩) l hl, l₀]
  have nA : ∀ x, x ∉ aregs → x ∉ aregs.take k := fun x hx h => hx (List.mem_of_mem_take h)
  have hm₁ : s₁.mem = s.mem := by rw [f₁.mem, m₀]
  have hrw₁ : s₁.rd ++ s₁.wr = s.rd ++ s.wr := by rw [f₁.rd, f₁.wr, rd₀, wr₀]
  have hsub : ∀ a : Addr, InRegions (s.rd ++ s.wr) a (16 * r) → ∀ i < k,
      InRegions (s₁.rd ++ s₁.wr) (a + BitVec.ofNat 64 (64 * i)) (if i + 1 = k then 16 * c' else 64) :=
    fun a h i hi => by
      rw [hrw₁]
      by_cases hik : i + 1 = k
      · rw [ite_eq_left hik]
        exact CallLay.inRegions_sub (off := 64 * i) (l := 16 * c') h (by omega) (by omega)
      · rw [ite_eq_right hik]
        exact CallLay.inRegions_sub (off := 64 * i) (l := 64) h (by omega) (by omega)
  have hE₁ : GEnvD k c' A W X' T' s₁ :=
    { rdx := by rw [f₁.gpr, g₀ _ (by decide)]; exact hA
      rax := by rw [f₁.gpr, g₀ _ (by decide)]; exact hW
      qk := by rw [f₁.gpr, a₀]; exact mq
      bk := by rw [f₁.gpr, a₀]; exact mb
      inA := hsub A (in_rdwr hinA)
      inW := hsub W hinW
      xs := fun i hi l hl _ => by
        show _ = blockAt s.mem (A + BitVec.ofNat 64 (16 * (4 * i + l)))
        rw [hm₁, blockAt_eq, Offset.add_add, show 64 * i + 16 * l = 16 * (4 * i + l) by omega]
      ts := fun i hi l hl => by
        show (if 4 * i + l < r then T (4 * i + l) else 0) = _
        by_cases ho : i + 1 < k ∨ l < c'
        · rw [ite_eq_left (show 4 * i + l < r by omega), ite_eq_left ho, hm₁, ← hT _ (by omega), Offset.add_add,
            show 64 * i + 16 * l = 16 * (4 * i + l) by omega]
        · rw [ite_eq_right (show ¬ 4 * i + l < r by omega), ite_eq_right ho]
      m0 := fun l hl => by rw [kz₁ _ (by decide) (nA _ (by decide)) l hl]; exact hmsk l hl }
  have hQ₁ : QGD k c' A W X' T' y 1 s₁ :=
    ⟨hE₁, fun l hl => by rw [kz₁ _ (by decide) (nA _ (by decide)) l hl]; exact h1 l hl, by
      rw [ite_eq_right (show ¬ 5 < 1 by omega)]
      exact ⟨fun h => absurd h (by decide), fun l hl => by rw [kz₁ _ (by decide) (nA _ (by decide)) l hl]; exact h2 l hl⟩⟩
  -- The rounds, the blocks hashed between them.
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 (aregs.take k) hnd' h13' hp.rounds (gD k) gRegs
    (fun r h hm => (gRegs_ok r h).1 (List.mem_of_mem_take hm)) (QGD k c' A W X' T' y)
    (fun j hj h9 t _ hq => WP.mono (WP.hkeep (gD_keeps k j) (gD_ok hk1 hk4 (by omega) j hj h9 t hq))
      fun _ ⟨⟨hq', hf⟩, hh⟩ => ⟨hq', hf, hh⟩)
    (fun j s s' h f => h.zframe f.toZFrame fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · have := List.mem_of_mem_take hr
        simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl | rfl <;> decide) s₁ hCache₁ hQ₁
    (by rw [f₁.gpr, g₀ _ (by decide), hrsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  obtain ⟨_, _, hY⟩ := hQ₂
  rw [ite_eq_left (show 5 < 10 by omega)] at hY
  -- The keystream blocks.
  have ks : ∀ n < r, XBinOp.eval .pshufb (s₂.zlane ((aregs.take k).getD (n / 4) .xmm0) (n % 4)) revMask =
      ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀)) := fun n hn => by
    have h : n / 4 < (aregs.take k).length := by rw [hlen]; omega
    rw [← List.getElem_eq_getD (h := h),
      (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) _ (by omega), e₁ _ h _ (by omega)])).symm,
      show c + 4 * (n / 4) + n % 4 = c + n by omega]
  have hg₂ : ∀ q, q ≠ .r10 → s₂.gpr q = s.gpr q := fun q hq => by rw [f₂.gpr, f₁.gpr, g₀ q hq]
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, hm₁]
  have hrd₂ : s₂.rd = s.rd := by rw [f₂.rd, f₁.rd, rd₀]
  have hwr₂ : s₂.wr = s.wr := by rw [f₂.wr, f₁.wr, wr₀]
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 (64 * 0) = a := fun a => BitVec.add_zero a
  have hc16 : 64 * ((aregs.take k).length - 1) + 16 * c' = 16 * r := by rw [hlen]; omega
  have hc4 : 4 * ((aregs.take k).length - 1) + c' = r := by rw [hlen]; omega
  have hA₂ : s₂.gpr .rdx = A := by rw [hg₂ _ (by decide)]; exact hA
  -- The blocks decrypted.
  refine WP.mono (xorG_ok .rdx (aregs.take k) 0 s₂ (c := c') (by
      intro h; rw [h] at hlen; simp at hlen; omega) hnd' h13' (by omega)
      (by rw [f₂.gpr, f₁.gpr, a₀]; exact mq) (by rw [f₂.gpr, f₁.gpr, a₀]; exact mb)
      (by rw [hA₂, e0, hc16, hrd₂, hwr₂]; exact in_rdwr hinA)
      (by rw [hA₂, e0, hc16, hwr₂]; exact hinA)
      (fun n q' hq hn => by
        rw [hA₂, Nat.mul_zero, Nat.zero_add, Nat.zero_add]
        rw [show A + BitVec.ofNat 64 (64 * q') = A + BitVec.ofNat 64 (16 * (4 * q')) by rw [← Nat.mul_assoc]]
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega))
      (by rw [hlen]; omega)) fun s' ⟨b', z', f', g', rd', wr', k'⟩ => ?_
  rw [hc4, hA₂] at b' z'
  rw [hc16, hA₂, e0] at f'
  simp only [Nat.mul_zero, Nat.zero_add] at b' z'
  have hy₂ : ∀ l < 4, s'.zlane .xmm2 l = s₂.zlane .xmm2 l := fun l hl =>
    k' _ (fun h => by
      have := List.mem_of_mem_take h
      simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h | h <;> cases h) (by decide) l hl
  refine ⟨fun n hn => ?_, by rw [← hm₂]; exact f', ?_, fun l h1 h4 => by rw [hy₂ l h4]; exact hY.2 l h1 h4,
    fun q hq => by rw [g', hg₂ q hq], by rw [rd', hrd₂], by rw [wr', hwr₂], fun x hx hx' l hl => ?_⟩
  · rw [b' n hn, hm₂, ks n hn]
  · rw [hy₂ 0 (by decide), hY.1]
    simp only [yLanes]
    rw [laneAccG_pad X' T y 0 r (4 * k) hrk, laneAccG_pad X' T y 1 r (4 * k) hrk,
      laneAccG_pad X' T y 2 r (4 * k) hrk, laneAccG_pad X' T y 3 r (4 * k) hrk]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    obtain ⟨n13, n14, n12, n7, n8, n9, n10, n11, n2⟩ := hx'
    rw [k' x (nA x hx) n13 l hl, f₂.zlane x (by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
      exact ⟨n13, nA x hx, n12, n7, n8, n9, n10, n11, n2⟩) l hl, kz₁ x n14 (nA x hx) l hl]

end VG.Proof.Gcm.X86_64.StitchZH
