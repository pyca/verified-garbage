module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGDHash
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.Slot
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGKs
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGXor
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Decryption: the blocks after the last group, as a masked group

`ksBatchGD_ok`: `StitchZH.ksBatchGD k` puts the mask of the last register's
blocks in `r10` (`remMaskG_ok`), encrypts the counters `c …` in the lanes of
`k` registers while it hashes the `r` ciphertext blocks at `rdx` between the
rounds (`gD_ok`), and adds the blocks to the keystream and stores them
(`xorG_ok`): the blocks decrypted in place, and `Y` their `GHASH` lanes,
reduced and added (`yLanes`). `ksSelGD_ok` runs it for the `⌈r / 4⌉`
registers the `r` blocks take, from `r10 = 16 r`. `remGD_ok`: once the
decryption loop stops with `r = nb mod 16` blocks left (`DInv`, the groups
already hashed and decrypted), `StitchZH.remGD` stores the counter after all
the blocks (`remSetup_ok`), decrypts the `r` blocks as a masked group, and
stores `Y`, for powers whose products add up to `GHASH` (`RemOkG`).
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
open VG.Proof.Gcm.X86_64.Stitch (SPre DPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀
  addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep')
open VG.Impl.Gcm.X86_64.Stitch (storeY)
open VG.Impl.Gcm.X86_64.StitchZH (ksSelGD remGD remSetupM)
open VG.Proof.Gcm.X86_64.StitchZ (DInv AInv)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (blocksAt ghashFrom)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq)
open VG.Proof.Gcm.X86_64.Pclmul (toNat_ofNat_lt)
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
    (hS : Slot.SlotOk (pp s₀) (cb s₀) (fun i => c + i) s.mem) (hr11 : s.gpr .r11 = pp s₀)
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask)
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
      (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm14, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
  have hwp := hp.wrap_p
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hnd' : (aregs.take k).Nodup := hnd.sublist (List.take_sublist _ _)
  have hx' : ∀ r ∈ aregs.take k, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := fun r hr => hx r (List.mem_of_mem_take hr)
  have h13' : .xmm13 ∉ aregs.take k := fun h => h13 (List.mem_of_mem_take h)
  have hlen : (aregs.take k).length = k := by simp [aregs]; omega_arith
  have hk1 : 1 ≤ k := by omega_arith
  let c' := (r - 1) % 4 + 1
  have hc : 4 * (k - 1) + c' = r := by omega_arith
  obtain ⟨mq, mb⟩ := maskG_ok c' (by omega_arith) (by omega_arith)
  have hK : Keys (nr s₀) (sch s₀) s := keys_of hp hrdi hrd hwr hfr
  -- The mask.
  refine WP.seq (WP.mono (WP.hkeepCode remMaskG_noCalls remMaskG_keeps (remMaskG_ok s hr1 (by omega_arith) h9))
    fun t ⟨⟨a₀, g₀, l₀, m₀, rd₀, wr₀⟩, hh₀⟩ => ?_)
  have hK₀ : Keys (nr s₀) (sch s₀) t :=
    keys_of hp (by rw [g₀ _ (by decide)]; exact hrdi) (by rw [rd₀]; exact hrd) (by rw [wr₀]; exact hwr)
      (by rw [m₀]; exact hfr)
  have hCache₀ := hCache.keep hh₀ hK₀
  -- The counters.
  refine WP.seq (WP.mono (WP.hkeep (loads_keeps _ _) (Slot.loads_ok (C := cb s₀) (f := fun i => c + i)
    (aregs.take k) 0 t (by rw [g₀ _ (by decide), m₀, hr11]; exact hS) (by omega_arith) hnd'
    (by rw [g₀ _ (by decide), rd₀, wr₀, hr11, hrd, hwr]; exact in_rdwr (in_sub hp.p_in (by decide)))))
    fun s₁ ⟨⟨e₁, f₁⟩, hh₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys hK₀ f₁
  have hCache₁ := hCache₀.keep hh₁ hK₁
  -- The GHASH environment of the rounds.
  let X' : Nat → Block := fun n => blockAt s.mem (A + BitVec.ofNat 64 (16 * n))
  let T' : Nat → BitVec 128 := fun n => if n < r then T n else 0
  have kz₁ : ∀ x, x ≠ .xmm14 → x ∉ aregs.take k → ∀ l < 4, s₁.zlane x l = s.zlane x l := fun x _ hx l hl => by
    rw [f₁.zlane x hx l hl, l₀]
  have nA : ∀ x, x ∉ aregs → x ∉ aregs.take k := fun x hx h => hx (List.mem_of_mem_take h)
  have hm₁ : s₁.mem = s.mem := by rw [f₁.mem, m₀]
  have hrw₁ : s₁.rd ++ s₁.wr = s.rd ++ s.wr := by rw [f₁.rd, f₁.wr, rd₀, wr₀]
  have hsub : ∀ a : Addr, InRegions (s.rd ++ s.wr) a (16 * r) → ∀ i < k,
      InRegions (s₁.rd ++ s₁.wr) (a + BitVec.ofNat 64 (64 * i)) (if i + 1 = k then 16 * c' else 64) :=
    fun a h i hi => by
      rw [hrw₁]
      by_cases hik : i + 1 = k
      · rw [ite_eq_left hik]
        exact CallLay.inRegions_sub (off := 64 * i) (l := 16 * c') h (by omega_arith) (by omega_arith)
      · rw [ite_eq_right hik]
        exact CallLay.inRegions_sub (off := 64 * i) (l := 64) h (by omega_arith) (by omega_arith)
  have hE₁ : GEnvD k c' A W X' T' s₁ :=
    { rdx := by rw [f₁.gpr, g₀ _ (by decide)]; exact hA
      rax := by rw [f₁.gpr, g₀ _ (by decide)]; exact hW
      qk := by rw [f₁.gpr, a₀]; exact mq
      bk := by rw [f₁.gpr, a₀]; exact mb
      inA := hsub A (in_rdwr hinA)
      inW := hsub W hinW
      xs := fun i hi l hl _ => by
        show _ = blockAt s.mem (A + BitVec.ofNat 64 (16 * (4 * i + l)))
        rw [hm₁, blockAt_eq, Offset.add_add, show 64 * i + 16 * l = 16 * (4 * i + l) by omega_arith]
      ts := fun i hi l hl => by
        show (if 4 * i + l < r then T (4 * i + l) else 0) = _
        by_cases ho : i + 1 < k ∨ l < c'
        · rw [ite_eq_left (show 4 * i + l < r by omega_arith), ite_eq_left ho, hm₁, ← hT _ (by omega_arith), Offset.add_add,
            show 64 * i + 16 * l = 16 * (4 * i + l) by omega_arith]
        · rw [ite_eq_right (show ¬ 4 * i + l < r by omega_arith), ite_eq_right ho]
      m0 := fun l hl => by rw [kz₁ _ (by decide) (nA _ (by decide)) l hl]; exact hmsk l hl }
  have hQ₁ : QGD k c' A W X' T' y 1 s₁ :=
    ⟨hE₁, fun l hl => by rw [kz₁ _ (by decide) (nA _ (by decide)) l hl]; exact h1 l hl, by
      rw [ite_eq_right (show ¬ 5 < 1 by omega_arith)]
      exact ⟨fun h => absurd h (by decide), fun l hl => by rw [kz₁ _ (by decide) (nA _ (by decide)) l hl]; exact h2 l hl⟩⟩
  -- The rounds, the blocks hashed between them.
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 (aregs.take k) hnd' h13' hp.rounds (gD k) gRegs
    (fun r h hm => (gRegs_ok r h).1 (List.mem_of_mem_take hm)) (QGD k c' A W X' T' y)
    (fun j hj h9 t _ hq => WP.mono (WP.hkeep (gD_keeps k j) (gD_ok hk1 hk4 (by omega_arith) j hj h9 t hq))
      fun _ ⟨⟨hq', hf⟩, hh⟩ => ⟨hq', hf, hh⟩)
    (fun j s s' h f => h.zframe f.toZFrame fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · have := List.mem_of_mem_take hr
        simp only [aregs, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl | rfl <;> decide) s₁ hCache₁ hQ₁
    (by rw [f₁.gpr, g₀ _ (by decide), hrsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  obtain ⟨_, _, hY⟩ := hQ₂
  rw [ite_eq_left (show 5 < 10 by omega_arith)] at hY
  -- The keystream blocks.
  have ks : ∀ n < r, XBinOp.eval .pshufb (s₂.zlane ((aregs.take k).getD (n / 4) .xmm0) (n % 4)) revMask =
      ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀)) := fun n hn => by
    have h : n / 4 < (aregs.take k).length := by rw [hlen]; omega_arith
    rw [← List.getElem_eq_getD (h := h),
      (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) _ (by omega_arith), e₁ _ h _ (by omega_arith)])).symm,
      show c + (4 * (0 + n / 4) + n % 4) = c + n by omega_arith]
  have hg₂ : ∀ q, q ≠ .r10 → s₂.gpr q = s.gpr q := fun q hq => by rw [f₂.gpr, f₁.gpr, g₀ q hq]
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, hm₁]
  have hrd₂ : s₂.rd = s.rd := by rw [f₂.rd, f₁.rd, rd₀]
  have hwr₂ : s₂.wr = s.wr := by rw [f₂.wr, f₁.wr, wr₀]
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 (64 * 0) = a := fun a => BitVec.add_zero a
  have hc16 : 64 * ((aregs.take k).length - 1) + 16 * c' = 16 * r := by rw [hlen]; omega_arith
  have hc4 : 4 * ((aregs.take k).length - 1) + c' = r := by rw [hlen]; omega_arith
  have hA₂ : s₂.gpr .rdx = A := by rw [hg₂ _ (by decide)]; exact hA
  -- The blocks decrypted.
  refine WP.mono (xorG_ok .rdx (aregs.take k) 0 s₂ (c := c') (by
      intro h; rw [h] at hlen; simp at hlen; omega_arith) hnd' h13' (by omega_arith)
      (by rw [f₂.gpr, f₁.gpr, a₀]; exact mq) (by rw [f₂.gpr, f₁.gpr, a₀]; exact mb)
      (by rw [hA₂, e0, hc16, hrd₂, hwr₂]; exact in_rdwr hinA)
      (by rw [hA₂, e0, hc16, hwr₂]; exact hinA)
      (fun n q' hq hn => by
        rw [hA₂, Nat.mul_zero, Nat.zero_add, Nat.zero_add]
        rw [show A + BitVec.ofNat 64 (64 * q') = A + BitVec.ofNat 64 (16 * (4 * q')) by rw [← Nat.mul_assoc]]
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
      (by rw [hlen]; omega_arith)) fun s' ⟨b', z', f', g', rd', wr', k'⟩ => ?_
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
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    obtain ⟨n13, n14, n12, n7, n8, n9, n10, n11, n2⟩ := hx'
    rw [k' x (nA x hx) n13 l hl, f₂.zlane x (by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
      exact ⟨n13, nA x hx, n12, n7, n8, n9, n10, n11, n2⟩) l hl, kz₁ x n14 (nA x hx) l hl]

/-- `add r9, 16`. -/
theorem add9_ok (s : State) :
    WP isa (.block [.alu .add .r9 (.imm 16)]) s fun s' =>
      s'.gpr .r9 = s.gpr .r9 + 16 ∧ (∀ q, q ≠ .r9 → s'.gpr q = s.gpr q) ∧ (∀ x l, s'.zlane x l = s.zlane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    State.setReg, e16, ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `ksBatchGD` of `⌈r / 4⌉` registers, from `r10 = 16 r`. -/
theorem ksSelGD_ok {s₀ : State} (hp : SPre s₀) {r : Nat} (hr1 : 1 ≤ r) (hr15 : r ≤ 15)
    {A W : Addr} {T : Nat → BitVec 128} {y : Block} {c : Nat} {s : State}
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hA : s.gpr .rdx = A) (hW : s.gpr .rax = W)
    (hT : ∀ n < r, s.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinA : InRegions s.wr A (16 * r)) (hinW : InRegions (s.rd ++ s.wr) W (16 * r))
    (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) (h2 : ∀ l < 4, s.zlane .xmm2 l = if l = 0 then y else 0)
    (hS : Slot.SlotOk (pp s₀) (cb s₀) (fun i => c + i) s.mem) (hr11 : s.gpr .r11 = pp s₀)
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask)
    (hrdi : s.gpr .rdi = kp s₀) (hrsi : s.gpr .rsi = s₀.gpr .rsi)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hfr : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s.mem)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa ksSelGD s fun s' =>
      (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
        blockAt s.mem (A + BitVec.ofNat 64 (16 * n)) ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
      Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
      s'.zlane .xmm2 0 = yLanes (fun n => blockAt s.mem (A + BitVec.ofNat 64 (16 * n))) T y r ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm14, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
  have br : ∀ k, r ≤ 4 * k → 4 * k < r + 4 → k ≤ 4 → ∀ t : State, t.gpr = s.gpr →
      (∀ x l, t.zlane x l = s.zlane x l) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → HKeep s t →
      WP isa (ksBatchGD k) t fun s' =>
        (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
          blockAt s.mem (A + BitVec.ofNat 64 (16 * n)) ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
        Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
        s'.zlane .xmm2 0 = yLanes (fun n => blockAt s.mem (A + BitVec.ofNat 64 (16 * n))) T y r ∧
        (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
        (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm14, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
    intro k hrk hkr hk4 t hg' hl hm hrd' hwr' hh
    have hm' : ∀ a : Addr, blockAt t.mem a = blockAt s.mem a := fun a => by rw [hm]
    refine WP.mono (ksBatchGD_ok hp hk4 hr1 hr15 hrk hkr (A := A) (W := W) (T := T) (y := y) (c := c)
      (by rw [hg']; exact h9) (by rw [hg']; exact hA) (by rw [hg']; exact hW) (fun n hn => by rw [hm]; exact hT n hn)
      (by rw [hwr']; exact hinA) (by rw [hrd', hwr']; exact hinW)
      (fun l hl' => by rw [hl]; exact h1 l hl') (fun l hl' => by rw [hl]; exact h2 l hl')
      (by rw [hm]; exact hS) (by rw [hg']; exact hr11) (fun l hl' => by rw [hl]; exact hmsk l hl')
      (by rw [hg']; exact hrdi) (by rw [hg']; exact hrsi)
      (by rw [hrd']; exact hrd) (by rw [hwr']; exact hwr) (by rw [hm]; exact hfr)
      (hCache.keep hh (Keys.mk (by rw [hg', hm]; exact (hCache.base).sched) hCache.base.le
        (by rw [hrd', hwr', hg']; exact hCache.base.keys))))
      fun s' ⟨b', f', y', y1', g', rd', wr', z'⟩ => ⟨fun n hn => by rw [b' n hn, hm' _], by rw [← hm]; exact f',
        by rw [y']; simp only [hm'], y1', fun q hq => by rw [g' q hq, hg'], by rw [rd', hrd'], by rw [wr', hwr'],
        fun x h1 h2 l hl' => by rw [z' x h1 h2 l hl', hl]⟩
  have c65 : BitVec.signExtend 64 (65 : BitVec 32) = BitVec.ofNat 64 65 := by decide
  have c129 : BitVec.signExtend 64 (129 : BitVec 32) = BitVec.ofNat 64 129 := by decide
  have c193 : BitVec.signExtend 64 (193 : BitVec 32) = BitVec.ofNat 64 193 := by decide
  have t16 : (s.gpr .r10).toNat = 16 * r := by rw [h10, toNat_ofNat_lt (by omega_arith)]
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s 65 65 c65)) fun s₁ ⟨⟨cf₁, g₁, l₁, m₁, rd₁, wr₁⟩, hh₁⟩ => ?_)
  rw [t16, show (BitVec.ofNat 64 65).toNat = 65 from rfl] at cf₁
  refine WP.ite (decide (16 * r < 65)) (by simp only [eval, cf₁]) (fun h => ?_) (fun h => ?_)
  · exact br 1 (by simp at h; omega_arith) (by simp at h; omega_arith) (by decide) s₁ g₁ l₁ m₁ rd₁ wr₁ hh₁
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s₁ 129 129 c129))
    fun s₂ ⟨⟨cf₂, g₂, l₂, m₂, rd₂, wr₂⟩, hh₂⟩ => ?_)
  rw [g₁, t16, show (BitVec.ofNat 64 129).toNat = 129 from rfl] at cf₂
  refine WP.ite (decide (16 * r < 129)) (by simp only [eval, cf₂]) (fun h' => ?_) (fun h' => ?_)
  · exact br 2 (by simp at h'; omega_arith) (by simp at h h'; omega_arith) (by decide) s₂ (by rw [g₂, g₁])
      (fun x l => by rw [l₂, l₁]) (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (hh₁.trans hh₂)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s₂ 193 193 c193))
    fun s₃ ⟨⟨cf₃, g₃, l₃, m₃, rd₃, wr₃⟩, hh₃⟩ => ?_)
  rw [g₂, g₁, t16, show (BitVec.ofNat 64 193).toNat = 193 from rfl] at cf₃
  refine WP.ite (decide (16 * r < 193)) (by simp only [eval, cf₃]) (fun h'' => ?_) (fun h'' => ?_)
  · exact br 3 (by simp at h''; omega_arith) (by simp at h' h''; omega_arith) (by decide) s₃ (by rw [g₃, g₂, g₁])
      (fun x l => by rw [l₃, l₂, l₁]) (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
      ((hh₁.trans hh₂).trans hh₃)
  · exact br 4 (by omega_arith) (by simp at h''; omega_arith) (by decide) s₃ (by rw [g₃, g₂, g₁])
      (fun x l => by rw [l₃, l₂, l₁]) (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
      ((hh₁.trans hh₂).trans hh₃)

theorem remGD_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hr : RemOkG (hk s₀) P) {e : Nat}
    {s : State} (hI : DInv s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq (.block [.alu .add .r9 (.imm 16)]) remGD) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have hle := hI.a.le
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by omega_arith
  have hr15 : r ≤ 15 := by omega_arith
  refine WP.seq (WP.mono (WP.hkeep (by decide) (add9_ok s)) fun s' ⟨⟨a9, ga, la, ma, rda, wra⟩, hha⟩ => ?_)
  have hr9 : s'.gpr .r9 = BitVec.ofNat 64 (16 + r) := by
    rw [a9, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
    congr 1; omega_arith
  have hrax : s'.gpr .rax = cp s₀ := by rw [ga _ (by decide)]; exact hI.rax
  have hr11 : s'.gpr .r11 = pp s₀ := by
    rw [ga _ (by decide)]; exact hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  have hA' : AInv s₀ (16 * e) s' :=
    hI.a.keep ma (fun q _ _ h3 => ga q h3) (fun l _ => la _ l) rda wra
  have hCache' := hCache.keep hha (hA'.keys hp)
  rw [show remGD = .seq (.block remSetupM) (.seq ksSelGD (.block storeY)) from rfl]
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (remSetupM_ok s' (C := cb s₀) (c := 16 * e) hr1 hr15 hr9
    (by rw [hr11]; exact hA'.slot)
    (by rw [hr11, hA'.rd, hA'.wr]; exact in_rdwr (in_sub hp.p_in (by decide)))
    (by rw [hrax, hA'.wr]; exact hp.c_in)
    (by rw [hrax, hr11]; exact hp.p_c.symm.sub_right (Gcm.X86_64.StitchZ.slot_sub s₀))))
    fun s₁ ⟨⟨b₁, fc₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  rw [hrax] at b₁ fc₁
  rw [ma] at fc₁
  have fcR : ∀ {R : Region}, Region.Disjoint R (cR s₀) → ∀ r ∈ [(⟨cp s₀, 16⟩ : Region)], Region.Disjoint R r :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
  have fc₁' : Frame [cR s₀] s.mem s₁.mem := fc₁
  rw [hr11] at ax₁
  have gk₁ : ∀ q, q ≠ .r10 → q ≠ .rax → q ≠ .r9 → s₁.gpr q = s.gpr q := fun q h1 h2 h3 => by
    rw [g₁ q h1 h2, ga q h3]
  have zk₁ : ∀ x, x ≠ .xmm13 → ∀ l < 4, s₁.zlane x l = s.zlane x l := fun x h l hl => by rw [z₁ x h l hl, la]
  have hfr₁ : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s₁.mem :=
    (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).trans
      (fc₁'.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
  have hrd₁ : s₁.rd = s₀.rd := by rw [rd₁, rda]; exact hI.a.rd
  have hwr₁ : s₁.wr = s₀.wr := by rw [wr₁, wra]; exact hI.a.wr
  have hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [gk₁ _ (by decide) (by decide) (by decide)]; exact hI.a.rdi
  have hCache₁ := hCache'.keep hh₁ (keys_of hp hrdi₁ hrd₁ hwr₁ hfr₁)
  -- The `r` blocks, hashed between the rounds and decrypted.
  let A := bAddr s₀ (16 * e)
  let W := pp s₀ + BitVec.ofNat 64 (256 - 16 * r)
  have hA : s₁.gpr .rdx = A := by
    rw [gk₁ _ (by decide) (by decide) (by decide), hI.rdx]
    show dp s₀ + BitVec.ofNat 64 (256 * e) = dp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [show 256 * e = 16 * (16 * e) by omega_arith]
  let y := ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))
  refine WP.seq (WP.mono (ksSelGD_ok hp hr1 hr15 (A := A) (W := W)
    (T := fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128) (y := y) (c := 16 * e) a10₁
    (by rw [g₁ _ (by decide) (by decide)]; exact hr9) hA ax₁ (fun _ _ => rfl)
    (by rw [hwr₁, show A = dp s₀ + BitVec.ofNat 64 (16 * (16 * e)) from rfl]; exact in_sub hp.d_in (by omega_arith))
    (by rw [hrd₁, hwr₁]; exact in_rdwr (in_sub hp.p_in (by omega_arith)))
    (fun l hl => by rw [zk₁ _ (by decide) l hl]; exact hI.m1 l hl)
    (fun l hl => by
      rw [zk₁ _ (by decide) l hl]
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · exact hI.y
      · rw [ite_eq_right_iff.2 (fun h => absurd h (by omega_arith))]; exact hI.y1 l hl0 hl)
    (hI.a.slot.frame fc₁ (fcR (hp.p_c.sub_left (Gcm.X86_64.StitchZ.slot_sub s₀))))
    (by rw [gk₁ _ (by decide) (by decide) (by decide), ← ga _ (by decide), hr11])
    (fun l hl => by rw [zk₁ _ (by decide) l hl]; exact hI.a.msk l hl) hrdi₁
    (by rw [gk₁ _ (by decide) (by decide) (by decide)]; exact hI.a.rsi) hrd₁ hwr₁ hfr₁ hCache₁)
    fun s₂ ⟨b₂, f₂, y₂, _, g₂, rd₂, wr₂, z₂⟩ => ?_)
  -- `Y` stored.
  have hrcx : s₂.gpr .rcx = yp s₀ := by
    rw [g₂ _ (by decide), gk₁ _ (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  have m0₂ : s₂.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), z₂ _ (by decide) (by decide) 0 (by decide), zk₁ _ (by decide) 0 (by decide)]
    exact hI.a.msk 0 (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (Gcm.X86_64.StitchZ.store16Z_ok .xmm2 .xmm2 .rcx s₂ m0₂
    (by rw [hrcx, wr₂, hwr₁]; exact hp.y_in))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx] at m₆
  have hnb : nb s₀ = 16 * e + r := by omega_arith
  have eA : ∀ j, A + BitVec.ofNat 64 (16 * j) = bAddr s₀ (16 * e + j) := fun j => by
    show bAddr s₀ (16 * e) + _ = _
    rw [Offset.add_add, ← Nat.mul_add]
  -- What the setup keeps of the memory before it.
  have toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) → blockAt s₁.mem p = blockAt s.mem p := fun p hc => by
    exact blockAt_frame fc₁ (fcR hc)
  have cP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_arith))
  have hS : ∀ j < r, blockAt s₁.mem (A + BitVec.ofNat 64 (16 * j)) = blk s₀ (16 * e + j) := fun j hj => by
    have hk : 16 * e + j < nb s₀ := by omega_arith
    rw [eA, toS _ (cP _ hk), hI.a.blocks _ hk]
    simp only [show ¬ 16 * e + j < 16 * e by omega_arith, ite_false]
  -- The blocks.
  have hb₂ : ∀ k < nb s₀, blockAt s₂.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame f₂ (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        toS _ (cP k hk), hI.a.blocks k hk]
      simp only [hke, ite_true]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_arith⟩
      have hj : j < r := by omega_arith
      rw [← eA, b₂ j hj, hS j hj]
  have hT : ∀ j < r, s₁.mem.readW (W + BitVec.ofNat 64 (16 * j)) 128 = P ((16 - r + j) / 4) ((16 - r + j) % 4) :=
    fun j hj => by
      have hm : 16 - r + j < 16 := by omega_arith
      rw [Offset.add_add, show 256 - 16 * r + 16 * j = 64 * ((16 - r + j) / 4) + 16 * ((16 - r + j) % 4) by omega_arith,
        fc₁.readW (Region.contains_self _ _) (fcR (hp.p_c.sub_left (Offset.sub_base _ (by omega_arith))))
          (by decide)]
      exact hI.pw _ (by omega_arith) _ (by omega_arith)
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega_arith))
  have hb : ∀ k < nb s₀, blockAt s₆.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yD k hk) rfl, hb₂ k hk]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₆.mem (cp s₀) = _
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.d_c.symm.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))),
      b₁, hnb]
  · show blockAt s₆.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
    have hbl : blocksAt s₀.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (blk s₀) := rfl
    have cg : ∀ l, laneAccG (fun n => blockAt s₁.mem (A + BitVec.ofNat 64 (16 * n)))
        (fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128) y l r =
        laneAccG (fun j => blk s₀ (16 * e + j)) (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4)) y l r :=
      fun l => laneAccG_congr _ l r hS hT
    rw [hbl, m₆, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (show 0 < 2 by decide), y₂]
    simp only [yLanes]
    rw [cg 0, cg 1, cg 2, cg 3, hr r hr1 hr15, hnb, List.range_add, List.map_append, List.map_map]
    simp only [y, ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₆.mem
    have F0 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    have F1 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s.mem s₁.mem :=
      fc₁'.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    have F2 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₁.mem s₂.mem := f₂.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith)⟩
    rw [m₆]
    exact ((F0.trans F1).trans F2).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4
    show s₆.gpr q = _
    rw [g₆, g₂ q h4, gk₁ q h4 h1 h3]
    exact hI.gpr q h1 h2 h3 h4
  · show s₆.rd = _
    rw [rd₆, rd₂]; exact hrd₁
  · show s₆.wr = _
    rw [wr₆, wr₂]; exact hwr₁

end VG.Proof.Gcm.X86_64.StitchZH
