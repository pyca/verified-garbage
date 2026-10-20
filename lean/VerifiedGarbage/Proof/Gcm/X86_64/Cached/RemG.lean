module
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGLanes
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGKs
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The blocks after the last group, as a masked group

`ksSelG_ok`: `StitchZH.ksSelG` runs `ksBatchG` (`ksBatchG_ok`) for the
`⌈r / 4⌉` registers the `r` blocks take, from `r10 = 16 r`. `remG_ok`: once
the loops stop with `r = nb mod 16` blocks after the groups encrypted, the
last group still to hash (`EInv`), `StitchZH.remG [] .rdx` stores the counter
after all the blocks (`remSetup_ok`), encrypts the `r` blocks as a masked
group while it hashes the last group, and reduces their products into `Y`,
for powers whose products add up to `GHASH` (`RemOkG`, which `StitchZ/OkP.lean`
proves of the powers the setup stores).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀
  addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep' ite_t ite_f)
open VG.Impl.Gcm.X86_64.Stitch (storeY)
open VG.Impl.Gcm.X86_64.StitchZH (remG ksSelG remSetup)
open VG.Proof.Gcm.X86_64.StitchZ (EInv GEnv QG gq_ok FinOk yNew)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (blocksAt ghashFrom)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Proof.Aes.X86_64.AesNi (Keys)

/-- `ksBatchG` of `⌈r / 4⌉` registers, from `r10 = 16 r`. -/
theorem ksSelG_ok {s₀ : State} (hp : SPre s₀) {r : Nat} (hr1 : 1 ≤ r) (hr15 : r ≤ 15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (Impl.Gcm.X86_64.StitchZ.gq j)) s fun s' => Q (j + 1) s' ∧ ZFrame StitchZ.gRegs s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    (pre : List Instr) (src : Reg) (hsrc : src ≠ .r10) (hs9 : src ≠ .r9) (hsa : src ≠ .rax)
    {A S W : Addr} {D T : Nat → Block} {y : Block} {c : Nat} {s : State}
    (hpre : ∀ t : State, t.gpr = s.gpr → WP isa (.block (.alu .add .rdx (.imm 256) :: pre)) t fun t' =>
      t'.gpr .rdx = A ∧ t'.gpr src = S ∧ (∀ q, q ≠ .rdx → q ≠ src → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.zlane x l = t.zlane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr)
    (hQ10 : ∀ t, Q 10 t → (∀ l < 4, t.zlane .xmm1 l = poly) ∧ ∀ l < 4, t.zlane .xmm2 l = if l = 0 then y else 0)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask) (hinc : ∀ l < 4, s.zlane .xmm15 l = four)
    (hrdi : s.gpr .rdi = kp s₀) (hrsi : s.gpr .rsi = s₀.gpr .rsi)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hfr : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s.mem)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) (hQ : Q 1 s)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hW : s.gpr .rax = W)
    (hD : ∀ n < r, blockAt s.mem (S + BitVec.ofNat 64 (16 * n)) = D n)
    (hT : ∀ n < r, s.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinS : InRegions (s.rd ++ s.wr) S (16 * r)) (hinD : InRegions s.wr A (16 * r))
    (hinW : InRegions (s.rd ++ s.wr) W (16 * r))
    (hsep : ∀ n q', q' < n / 4 → n < r →
      Region.Disjoint ⟨S + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A + BitVec.ofNat 64 (64 * q'), 64⟩)
    (hWA : ∀ n < r, Region.Disjoint ⟨W + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A, 16 * r⟩) :
    WP isa (Impl.Gcm.X86_64.StitchZH.ksSelG pre src) s fun s' =>
      (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
        D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
      Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
      s'.zlane .xmm2 0 =
        (reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 0 r) ^^^
          reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 2 r)) ^^^
        (reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 1 r) ^^^
          reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 3 r)) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → q ≠ .rdx → q ≠ src → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) →
        x ≠ .xmm14 → x ∉ StitchZ.gRegs → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
  -- A batch of `k` registers, from a state the comparisons leave as `s` was.
  have br : ∀ k, r ≤ 4 * k → 4 * k < r + 4 → k ≤ 4 → ∀ t : State, t.gpr = s.gpr →
      (∀ x l, t.zlane x l = s.zlane x l) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → HKeep s t →
      WP isa (Impl.Gcm.X86_64.StitchZH.ksBatchG k Impl.Gcm.X86_64.StitchZ.gq pre src) t fun s' =>
        (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
          D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
        Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
        s'.zlane .xmm2 0 =
          (reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 0 r) ^^^
            reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 2 r)) ^^^
          (reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 1 r) ^^^
            reduceB (laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 3 r)) ∧
        (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
        (∀ q, q ≠ .r10 → q ≠ .rdx → q ≠ src → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (∀ x, x ∉ aregs → x ∉ ([.xmm13, .xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] : List XReg) →
          x ≠ .xmm14 → x ∉ StitchZ.gRegs → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
    intro k hrk hkr hk4 t hg' hl hm hrd' hwr' hh
    have hQt : Q 1 t := hq 1 s t hQ ⟨hg', hm, hrd', hwr', fun x _ l _ => hl x l⟩
    refine WP.mono (ksBatchG_ok hp hk4 hr1 hr15 hrk hkr _ StitchZ.gRegs StitchZ.gRegs_ok Q hg hq pre src hsrc hs9 hsa
      (A := A) (S := S) (W := W) (D := D) (T := T) (c := c)
      (fun t' h => hpre t' (h.trans hg')) hQ10
      (fun l hl' => by rw [hl]; exact hctr l hl') (fun l hl' => by rw [hl]; exact hmsk l hl')
      (fun l hl' => by rw [hl]; exact hinc l hl') (by rw [hg']; exact hrdi) (by rw [hg']; exact hrsi)
      (by rw [hrd']; exact hrd) (by rw [hwr']; exact hwr) (by rw [hm]; exact hfr)
      (hCache.keep hh (Keys.mk (by rw [hg', hm]; exact (hCache.base).sched) hCache.base.le
        (by rw [hrd', hwr', hg']; exact hCache.base.keys))) gq_keeps hQt
      (by rw [hg']; exact h9) (by rw [hg']; exact hW) (fun n hn => by rw [hm]; exact hD n hn)
      (fun n hn => by rw [hm]; exact hT n hn) (by rw [hrd', hwr']; exact hinS) (by rw [hwr']; exact hinD)
      (by rw [hrd', hwr']; exact hinW) hsep hWA)
      fun s' ⟨b', f', y', y1', g', rd', wr', z'⟩ => ⟨b', by rw [← hm]; exact f', y', y1',
        fun q h1 h2 h3 => by rw [g' q h1 h2 h3, hg'], by rw [rd', hrd'], by rw [wr', hwr'],
        fun x h1 h2 h3 h4 l hl' => by rw [z' x h1 h2 h3 h4 l hl', hl]⟩
  have c65 : BitVec.signExtend 64 (65 : BitVec 32) = BitVec.ofNat 64 65 := by decide
  have c129 : BitVec.signExtend 64 (129 : BitVec 32) = BitVec.ofNat 64 129 := by decide
  have c193 : BitVec.signExtend 64 (193 : BitVec 32) = BitVec.ofNat 64 193 := by decide
  have t16 : (s.gpr .r10).toNat = 16 * r := by
    rw [h10, VG.Proof.Gcm.X86_64.Pclmul.toNat_ofNat_lt (by omega_using [hr15])]
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s 65 65 c65)) fun s₁ ⟨⟨cf₁, g₁, l₁, m₁, rd₁, wr₁⟩, hh₁⟩ => ?_)
  rw [t16, show (BitVec.ofNat 64 65).toNat = 65 from rfl] at cf₁
  refine WP.ite (decide (16 * r < 65)) (by simp only [eval, cf₁]) (fun h => ?_) (fun h => ?_)
  · exact br 1 (by simp at h; omega_using [h]) (by simp at h; omega_using [hr1]) (by decide) s₁ g₁ l₁ m₁ rd₁ wr₁ hh₁
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s₁ 129 129 c129))
    fun s₂ ⟨⟨cf₂, g₂, l₂, m₂, rd₂, wr₂⟩, hh₂⟩ => ?_)
  rw [g₁, t16, show (BitVec.ofNat 64 129).toNat = 129 from rfl] at cf₂
  refine WP.ite (decide (16 * r < 129)) (by simp only [eval, cf₂]) (fun h' => ?_) (fun h' => ?_)
  · exact br 2 (by simp at h'; omega_using [h']) (by simp at h h'; omega_using [h]) (by decide) s₂ (by rw [g₂, g₁])
      (fun x l => by rw [l₂, l₁]) (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (hh₁.trans hh₂)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp10_ok s₂ 193 193 c193))
    fun s₃ ⟨⟨cf₃, g₃, l₃, m₃, rd₃, wr₃⟩, hh₃⟩ => ?_)
  rw [g₂, g₁, t16, show (BitVec.ofNat 64 193).toNat = 193 from rfl] at cf₃
  refine WP.ite (decide (16 * r < 193)) (by simp only [eval, cf₃]) (fun h'' => ?_) (fun h'' => ?_)
  · exact br 3 (by simp at h''; omega_using [h'']) (by simp at h' h''; omega_using [h']) (by decide) s₃ (by rw [g₃, g₂, g₁])
      (fun x l => by rw [l₃, l₂, l₁]) (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
      ((hh₁.trans hh₂).trans hh₃)
  · exact br 4 (by omega_using [hr15]) (by simp at h''; omega_using [h'']) (by decide) s₃ (by rw [g₃, g₂, g₁])
      (fun x l => by rw [l₃, l₂, l₁]) (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
      ((hh₁.trans hh₂).trans hh₃)

/-- `add rdx, 256`. -/
theorem addRdx_ok (t : State) :
    WP isa (.block [.alu .add .rdx (.imm 256)]) t fun t' =>
      t'.gpr .rdx = t.gpr .rdx + 256 ∧ (∀ q, q ≠ .rdx → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.zlane x l = t.zlane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, e256, ↓reduceIte,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

theorem remG_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOkG (hk s₀) P) {e : Nat} {s : State} (hI : EInv s₀ P e s) (hex : nb s₀ - 16 * (e - 1) < 32)
    (hne : nb s₀ ≠ 16 * e) (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (remG [] .rdx) s (EPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hle := hI.a.le
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  -- The `r` blocks after the `16 e` encrypted.
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by omega_using [hne, hle, hr_def]
  have hr15 : r ≤ 15 := by omega_using [hex, h1e, hr_def]
  have hr9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r) := by rw [hI.r9]; congr 1; omega_using [h1e, hr_def, hr1]
  have hrax : s.gpr .rax = cp s₀ := hI.rax
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  rw [show remG [] .rdx = .seq (.block remSetup) (.seq (ksSelG [] .rdx) (.block storeY)) from rfl]
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (remSetup_ok s hr1 hr15 hr9
    (by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide))
    (by rw [hrax, hI.a.wr]; exact in_sub_int hp.c_in (by omega_using []))))
    fun s₁ ⟨⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  have e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hrax, e0] at m₁
  rw [hr11] at ax₁
  have gk₁ : ∀ q, q ≠ .r10 → q ≠ .rax → s₁.gpr q = s.gpr q := g₁
  have cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  have hfr₁ : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  have hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [gk₁ _ (by decide) (by decide)]; exact hI.a.rdi
  have hCache₁ := hCache.keep hh₁ (keys_of hp hrdi₁ (by rw [rd₁]; exact hI.a.rd) (by rw [wr₁]; exact hI.a.wr) hfr₁)
  -- The last group, hashed while the `r` blocks are encrypted.
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hE₁ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [gk₁ _ (by decide) (by decide)]
      r11 := by rw [gk₁ _ (by decide) (by decide), hr11]
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega_using [ha]), m₁,
          show cp s₀ = (cR s₀).base from rfl,
          blockAt_writeW_sep' (hp.d_c.sub_left (Offset.sub_base _ (by omega_using [h1e, hle, hi]))) rfl,
          hI.a.blocks _ (by omega_using [h1e, hle, hi])]
        simp only [show 16 * (e - 1) + i < 16 * e by omega_using [h1e, hi], ite_true]
        rfl
      pv := fun k hk l hl => by
        rw [m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega_using [hk, hl]))).sep
          (Region.contains_self _ _) cw) (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega_using [ha])]
        exact in_rdwr (in_sub hp.d_in (by omega_using [h1e, hle, hk]))
      inp := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_using [hk]))
      m0 := fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  have hQ₁ : QG s₀ (fun _ => 0) a X P yl 1 s₁ :=
    ⟨hE₁, fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [z₁ _ (by decide) l hl]⟩⟩
  -- Where the `r` blocks and their powers are.
  let A := bAddr s₀ (16 * e)
  let W := pp s₀ + BitVec.ofNat 64 (256 - 16 * r)
  have hA : a + 256 = A := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (show a.toNat + 256 < 2 ^ 64 by omega_using [hne, hw, h1e, hle, ha]), BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 16 * (16 * e) < 2 ^ 64 by omega_using [hne, hw, hle]), Nat.mod_eq_of_lt (by omega_using [hne, hw, hle])]
    omega_using [h1e, ha]
  have hrd₁ : s₁.rd = s₀.rd := by rw [rd₁, hI.a.rd]
  have hwr₁ : s₁.wr = s₀.wr := by rw [wr₁, hI.a.wr]
  have eA : ∀ j, A + BitVec.ofNat 64 (16 * j) = bAddr s₀ (16 * e + j) := fun j => by
    show bAddr s₀ (16 * e) + _ = _
    rw [Offset.add_add, ← Nat.mul_add]
  have hQ10 : ∀ t, QG s₀ (fun _ => 0) a X P yl 10 t → (∀ l < 4, t.zlane .xmm1 l = poly) ∧
      ∀ l < 4, t.zlane .xmm2 l = if l = 0 then yNew X P yl else 0 := fun t ⟨_, h1, h2⟩ => by
    rw [ite_t (by decide)] at h2
    refine ⟨h1, fun l hl => ?_⟩
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · exact h2.1
    · rw [ite_eq_right_iff.2 (fun h => absurd h (by omega_using [hl0]))]; exact h2.2 l hl0 hl
  refine WP.seq (WP.mono (ksSelG_ok hp hr1 hr15 (QG s₀ (fun _ => 0) a X P yl)
    (gq_ok (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide)) [] .rdx (by decide) (by decide) (by decide)
    (A := A) (S := A) (W := W) (D := fun n => blockAt s₁.mem (A + BitVec.ofNat 64 (16 * n)))
    (T := fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128) (c := 16 * e)
    (fun t ht => WP.mono (addRdx_ok t) fun t' ⟨d', g', l', m', rd', wr'⟩ =>
      ⟨by rw [d', ht, gk₁ _ (by decide) (by decide)]; exact hA, by rw [d', ht, gk₁ _ (by decide) (by decide)]; exact hA,
        fun q h _ => g' q h, l', m', rd', wr'⟩)
    hQ10 a10₁ (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.inc l hl) hrdi₁
    (by rw [gk₁ _ (by decide) (by decide)]; exact hI.a.rsi) hrd₁ hwr₁ hfr₁ hCache₁ hQ₁
    (by rw [gk₁ _ (by decide) (by decide)]; exact hr9) ax₁ (fun _ _ => rfl) (fun _ _ => rfl)
    (by rw [hrd₁, hwr₁, show A = dp s₀ + BitVec.ofNat 64 (16 * (16 * e)) from rfl]
        exact in_rdwr (in_sub hp.d_in (by omega_using [hr_def, hr1])))
    (by rw [hwr₁, show A = dp s₀ + BitVec.ofNat 64 (16 * (16 * e)) from rfl]
        exact in_sub hp.d_in (by omega_using [hr_def, hr1]))
    (by rw [hrd₁, hwr₁]; exact in_rdwr (in_sub hp.p_in (by omega_using [hr15])))
    (fun n q' hq hn => by
      rw [eA, show A + BitVec.ofNat 64 (64 * q') = bAddr s₀ (16 * e + 4 * q') by
        show bAddr s₀ (16 * e) + _ = _; rw [Offset.add_add]; congr 2; omega_using []]
      exact Offset.disjoint _ (.inr (by omega_using [hq])) (by omega_arith) (by omega_arith))
    (fun n hn => by
      show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * n), 16⟩
        ⟨bAddr s₀ (16 * e), 16 * r⟩
      rw [Offset.add_add]
      exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))))
    fun s₂ ⟨b₂, f₂, y₂, _, g₂, rd₂, wr₂, z₂⟩ => ?_)
  -- `Y` after the groups.
  have hY : yNew X P yl = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀)) := by
    rw [hf X yl hI.y1, show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega_using [h1e],
      VG.Proof.Gcm.X86_64.Stitch.ghash_append16, ← hI.y]
  -- `Y` stored.
  have hrcx : s₂.gpr .rcx = yp s₀ := by
    rw [g₂ _ (by decide) (by decide) (by decide), gk₁ _ (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  have m0₂ : s₂.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), z₂ _ (by decide) (by decide) (by decide) (by decide) 0 (by decide),
      z₁ _ (by decide) 0 (by decide)]
    exact hI.a.msk 0 (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (Gcm.X86_64.StitchZ.store16Z_ok .xmm2 .xmm2 .rcx s₂ m0₂
    (by rw [hrcx, wr₂, hwr₁]; exact hp.y_in))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx] at m₆
  have hnb : nb s₀ = 16 * e + r := by omega_using [hr_def, hr1]
  -- What the setup keeps of the memory before it.
  have toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) → blockAt s₁.mem p = blockAt s.mem p := fun p hc => by
    rw [m₁, show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  have cP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_using [hk]))
  -- The `r` blocks, encrypted.
  have hX : ∀ j < r, blockAt s₁.mem (A + BitVec.ofNat 64 (16 * j)) ^^^
      ciph s₀ (Nat.repeat inc32 (16 * e + j) (cb s₀)) = ctb s₀ (16 * e + j) := fun j hj => by
    have hk : 16 * e + j < nb s₀ := by omega_using [hnb, hj]
    rw [eA, toS _ (cP _ hk), hI.a.blocks _ hk]
    simp only [show ¬ 16 * e + j < 16 * e by omega_using [], ite_false]
  -- The blocks.
  have hb₂ : ∀ k < nb s₀, blockAt s₂.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame f₂ (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega_using [hke])) (by omega_using [ha, hke]) (by omega_using [hw, hnb])),
        toS _ (cP k hk), hI.a.blocks k hk]
      simp only [hke, ite_true]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_using [hke]⟩
      have hj : j < r := by omega_using [hnb, hk]
      rw [← eA, b₂ j hj, hX j hj]
  have hT : ∀ j < r, s₁.mem.readW (W + BitVec.ofNat 64 (16 * j)) 128 = P ((16 - r + j) / 4) ((16 - r + j) % 4) :=
    fun j hj => by
      have hm : 16 - r + j < 16 := by omega_using [hr15, hj]
      rw [Offset.add_add, show 256 - 16 * r + 16 * j = 64 * ((16 - r + j) / 4) + 16 * ((16 - r + j) % 4) by omega_using [],
        m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega_using [hm]))).sep
            (Region.contains_self _ _) cw) (by decide)]
      exact hI.pw _ (by omega_using [hm]) _ (by omega_using [])
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega_using [hk]))
  have hb : ∀ k < nb s₀, blockAt s₆.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yD k hk) rfl, hb₂ k hk]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₆.mem (cp s₀) = _
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.d_c.symm.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_using [hnb]))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), hI.a.ctr 0 (by decide),
      Nat.add_zero, VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₆.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₆.mem (dp s₀) (nb s₀))
    have hbl : blocksAt s₆.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (ctb s₀) := by
      simp only [blocksAt]
      exact List.map_congr_left fun k hk => hb k (by simpa using hk)
    have cg : ∀ l, laneAccG (fun n => blockAt s₁.mem (A + BitVec.ofNat 64 (16 * n)) ^^^
        ciph s₀ (Nat.repeat inc32 (16 * e + n) (cb s₀))) (fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128)
        (yNew X P yl) l r = laneAccG (fun j => ctb s₀ (16 * e + j)) (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4))
        (yNew X P yl) l r := fun l => laneAccG_congr _ l r hX hT
    rw [hbl, m₆, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (show 0 < 2 by decide), y₂, cg 0, cg 1,
      cg 2, cg 3, hr r hr1 hr15, hY, hnb, List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₆.mem
    have F0 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    have F1 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    have F2 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₁.mem s₂.mem := f₂.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_using [hnb])⟩
    rw [m₆]
    exact ((F0.trans F1).trans F2).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4
    show s₆.gpr q = _
    rw [g₆, g₂ q h4 h2 h2, gk₁ q h4 h1]
    exact hI.gpr q h1 h2 h3 h4
  · show s₆.rd = _
    rw [rd₆, rd₂]; exact hrd₁
  · show s₆.wr = _
    rw [wr₆, wr₂]; exact hwr₁

/-- The end of `encR`: the last group, and the blocks after it if any. -/
theorem tailR_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOkG (hk s₀) P) {e : Nat} {s : State} (hI : EInv s₀ P e s) (hex : nb s₀ - 16 * (e - 1) < 32)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (Impl.Gcm.X86_64.StitchZH.tailR Impl.Gcm.X86_64.StitchZH.rem) s (EPost s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have h1e := hI.one
  have hle := hI.a.le
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp16_ok s)) fun s₁ ⟨⟨zf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₁ := hI.of_eq g l m rd wr
  have hz : (s.gpr .r9 - 16 == 0) = decide (nb s₀ = 16 * e) := by
    rw [hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega_using [h1e, hle]) (by omega_using [hn])]
    by_cases h : nb s₀ = 16 * e
    · rw [show nb s₀ - 16 * (e - 1) - 16 = 0 by omega_using [h], decide_eq_true h]; rfl
    · have : BitVec.ofNat 64 (nb s₀ - 16 * (e - 1) - 16) ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega_using [h1e, hle, h, this, h0]
      rw [beq_false_of_ne this, decide_eq_false h]
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, zf, hz]) (fun h => ?_) (fun h => ?_)
  · exact Gcm.X86_64.StitchZ.final_ok hp hf (by simpa using h) hI₁
  · exact remG_ok hp hf hr hI₁ hex (by simpa using h) (hCache.keep hh (hI₁.a.keys hp))

/-- `encR` after the setup, for any number of blocks from 16 on. -/
theorem encTailRG_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOkG (hk s₀) P)
    {bigC : Prog isa} {i : BitVec 32} (t : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 t)
    (ht : t < 2 ^ 64) (hbig : ∀ s, t ≤ nb s₀ → EInv s₀ P 1 s → VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s →
      WP isa bigC s fun s' => ∃ e, EInv s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s')
    {s : State} (hR : Gcm.X86_64.StitchZ.Ready s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq Impl.Gcm.X86_64.StitchZH.first (.seq (.block [.alu .cmp .r9 (.imm i)])
      (.seq (.ite .b (.block []) bigC) (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop Impl.Gcm.X86_64.StitchZH.body .ae))
          (Impl.Gcm.X86_64.StitchZH.tailR Impl.Gcm.X86_64.StitchZH.rem)))))) s (EPost s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (first_ok hp hR hCache) fun s₂ ⟨hI₂, hCache₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep rfl (Gcm.X86_64.StitchZ.cmp_ok s₂ i t hi))
    fun s₃ ⟨⟨hcf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₃ := hI₂.of_eq g l m rd wr
  have hCache₃ := hCache₂.keep hh (hI₃.a.keys hp)
  rw [hI₂.r9, VG.Proof.Gcm.X86_64.Pclmul.toNat_ofNat_lt (by omega_using [hn]),
    VG.Proof.Gcm.X86_64.Pclmul.toNat_ofNat_lt ht] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, EInv s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * (1 - 1) < t))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨1, hI₃, hCache₃⟩)
    (fun h => hbig _ (by simp at h; omega_using [h]) hI₃ hCache₃)) fun s₄ ⟨e, hI₄, hCache₄⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (Gcm.X86_64.StitchZ.cmpE_ok hI₄)) fun s₅ ⟨⟨hI₅, hcf₅⟩, hh₅⟩ => ?_)
  exact WP.seq (WP.mono (loopER_ok hp hf hI₅ hcf₅ (hCache₄.keep hh₅ (hI₅.a.keys hp)))
    fun s₆ ⟨e, hex, hI₆, hC₆⟩ => tailR_ok hp hf hr hI₆ hex hC₆)
end VG.Proof.Gcm.X86_64.StitchZH
