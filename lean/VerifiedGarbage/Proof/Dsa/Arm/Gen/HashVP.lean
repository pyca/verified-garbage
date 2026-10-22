module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Hash
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # DSA parameter generation on ARMv7: the hash of the block at `sMsg`, as a piece -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_movw wp_mov wp_dp wp_str op2_reg op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {Gh : Hash} (HO : HashOk Gh)

/-- After the initial hash value and the pointers. -/
abbrev H1 (F : State → State → Prop) (σ s : State) : Prop :=
  ∃ s₀, F σ s₀ ∧ Rest [.r0, .r1, .r2, .r3, .r12] s₀ s ∧ Frame [G.rs sState (4 * Gh.k)] s₀.mem s.mem ∧
    (∀ j (hj : j < Gh.iv.length), s.mem.readW (G.sa sState + BitVec.ofNat 64 (4 * j)) 32 = Gh.iv[j]) ∧
    s.gpr .r0 = G.scr + BitVec.ofNat 32 sState ∧ s.gpr .r1 = G.scr + BitVec.ofNat 32 sMsg ∧
    s.gpr .r3 = G.scr + BitVec.ofNat 32 sA

/-- After the compression. -/
abbrev H2 (F : State → State → Prop) (σ s : State) : Prop :=
  ∃ s₀, F σ s₀ ∧ Rest [.r0, .r1, .r2, .r3, .r12, .lr] s₀ s ∧
    Frame [G.rs sState (4 * Gh.k), G.rs sA 112] s₀.mem s.mem ∧
    HO.md.stateAt s.mem (G.sa sState) = HO.md.compress HO.H0 (HO.md.blockAt s₀.mem (G.sa sMsg)) ∧
    s.gpr .r0 = G.scr + BitVec.ofNat 32 sState

include HO in
theorem hash1_vp {F : State → State → Prop} {c : State → Cfg} {L : Nat}
    (hF : ∀ σ s, F σ s → SS G σ (c σ) s) (hL : L = G.pLen) :
    VP F (.block (scr L .r0 sState ++ ivStore Gh.iv ++ scr L .r1 sMsg ++ scr L .r3 sA)) (H1 (G := G) (Gh := Gh) F) := by
  refine VP.taint [.r8] (HO.cert1 L) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).r8, (hF _ _ h₂).r8]
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have hLv := h.lens
  have hk := HO.hk
  have il := HO.ivLen
  subst hL
  simp only [List.append_assoc]
  refine scr_ok (d := .r0) h.r8 rfl hLv (by simp only [sK, sA, wa, sState]; omega) fun s₁ v₁ R₁ M₁ => ?_
  rw [ivStore_eq]
  have e₀ : State.addr (G.scr + BitVec.ofNat 32 sState) = G.sa sState := h.addr (n := 32)
    (by simp only [sK, sA, wa, sState]; omega) (by decide)
  have tn := h.toNat (o := sState) (by simp only [sK, sA, wa, sState]; omega)
  have e64 : sState = 64 := rfl
  have kzp : 0 < kz G.pLen := by simp only [kz]; omega
  have sk4 : 4096 ≤ sK G.pLen := by simp only [sK, sA]; omega
  refine ivAt_ok (R := G.rScr) Gh.iv 0 s₁ _ _ v₁ (by omega) (by rw [tn]; omega)
    (by rw [R₁.wr, gi.wr, gi.pre.wr, gi.hG]; simp) (fun j hj => ?_) fun s₂ R₂ F₂ W₂ => ?_
  · rw [e₀, Nat.zero_add, Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  have r8₂ : s₂.gpr .r8 = G.KB := by rw [R₂.gpr _ (by decide), R₁.gpr _ (by decide), h.r8]
  refine scr_ok (d := .r1) r8₂ rfl hLv (by simp only [sK, sA, wa, sMsg]; omega) fun s₃ v₃ R₃ M₃ => ?_
  refine scr_ok (d := .r3) (by rw [R₃.gpr _ (by decide), r8₂]) rfl hLv (by simp only [sK, sA, wa]; omega)
    fun t v₄ R₄ M₄ => WP.block_nil ⟨s, hs, ?_, ?_, fun j hj => ?_, ?_, ?_, v₄⟩
  · exact ((R₁.mono (by simp)).trans (R₂.mono (by simp))).trans ((R₃.mono (by simp)).trans (R₄.mono (by simp)))
  · rw [M₄, M₃, ← M₁]
    show Frame [⟨G.sa sState, 4 * Gh.k⟩] _ _
    rw [← e₀, ← il]
    simpa only [Nat.mul_zero, BitVec.add_zero, e₀] using F₂
  · rw [M₄, M₃, ← e₀]
    simpa only [Nat.zero_add] using W₂ j hj
  · rw [R₄.gpr _ (by decide), R₃.gpr _ (by decide), R₂.gpr _ (by decide)]; exact v₁
  · rw [R₄.gpr _ (by decide)]; exact v₃

/-- A call that keeps `r4`–`r11` keeps all but `r0`–`r3`, `r12` and `lr`. -/
theorem rest_of_preserved {s s' : State} (g : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) :
    Rest [.r0, .r1, .r2, .r3, .r12, .lr] s s' :=
  ⟨fun r hr => g r (by cases r <;> simp_all [preserved]) (by rintro rfl; simp at hr), rd, wr, sp⟩

/-- The block's bytes, as the compression function reads it. -/
theorem blockAt_eq {m : Mem} {p : Addr} {bs : List Byte} (h : Spec.Rsa.bytesAt m p 64 = bs) :
    HO.md.blockAt m p = HO.md.parse fun t => bs.getD t 0 := by
  unfold VG.Proof.MdStream.Md.blockAt
  refine HO.md.parse_congr fun k hk => ?_
  rw [HO.hB] at hk
  rw [← h]
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hk]

theorem hash2_vp {F : State → State → Prop} {c : State → Cfg}
    (hF : ∀ σ s, F σ s → SS G σ (c σ) s) :
    VP (fun σ s => H1 (G := G) (Gh := Gh) F σ s ∧ s.gpr .r2 = 1) (.call Gh.name Gh.code) (H2 HO (G := G) F) := by
  -- The regions the compression function is given.
  let rd : List Region := [⟨G.sa sMsg, HO.P.B * 1⟩]
  let wr : List Region := [⟨G.sa sState, HO.P.N⟩, ⟨G.sa sA, HO.P.so⟩]
  have facts : ∀ σ s, H1 (G := G) (Gh := Gh) F σ s → s.gpr .r2 = 1 →
      (MdStream.Arm.compressK HO.md).pre (s.callEntry.withRegions rd wr) ∧ Covers (rd ++ wr) (s.rd ++ s.wr) ∧
        Covers wr s.wr := by
    intro σ s ⟨s₀, hs₀, R, _, _, e0, e1, e3⟩ e2
    have h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.scrBig
    have fit := gi.scrFit
    have kzp : 0 < kz G.pLen := by simp only [kz]; omega
    have sk4 : 4096 + 640 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega
    have hB := HO.hB; have hN := HO.hN; have hso := HO.hso; have hk := HO.hk
    have a0 := h.addr (o := sState) (n := 32) (by simp only [sState]; omega) (by decide)
    have a1 := h.addr (o := sMsg) (n := 64) (by simp only [sMsg]; omega) (by decide)
    have a3 := h.addr (o := sA) (n := 112) (by simp only [sA]; omega) (by decide)
    have t0 := h.toNat (o := sState) (by simp only [sState]; omega)
    have t1 := h.toNat (o := sMsg) (by simp only [sMsg]; omega)
    have t3 := h.toNat (o := sA) (by simp only [sA]; omega)
    have ws : s.wr = s₀.wr := R.wr
    have rds : s.rd = s₀.rd := R.rd
    have hw : Covers wr s.wr := by
      rw [ws]
      refine Covers.pair (Covers.one (gi.inScr ?_)) (Covers.one (gi.inScr ?_)) <;>
        simp only [sState, sA, hN, hso] <;> omega
    refine ⟨?_, Covers.append_left (Covers.right (Covers.one (by
      rw [ws]; exact gi.inScr (by simp only [sMsg, hB]; omega)))) hw.right, hw⟩
    simp only [MdStream.Arm.compressK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
      e0, e1, e2, e3, a0, a1, a3, t0, t1, t3]
    have one : (1 : BitVec 32).toNat = 1 := rfl
    have n0 : sState = 64 := rfl
    have n1 : sMsg = 0 := rfl
    have n3 : sA = 4096 := rfl
    rw [one, hB, hN, hso]
    refine ⟨by simp [rd, hB], by simp [wr, hN, hso], gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_,
      ?_, ?_, ?_⟩ <;> omega
  refine VP.of_ct (fun σ₁ σ₂ => RelCT.call HO.callee.verified HO.ct rd wr fun s₁ s₂ ⟨⟨h₁, r₁⟩, ⟨h₂, r₂⟩⟩ => ?_)
    fun σ s ⟨h₁, r₂⟩ => ?_
  · obtain ⟨p₁, c₁, w₁⟩ := facts σ₁ s₁ h₁ r₁
    obtain ⟨p₂, c₂, w₂⟩ := facts σ₂ s₂ h₂ r₂
    obtain ⟨_, _, _, _, _, e0, e1, e3⟩ := h₁
    obtain ⟨_, _, _, _, _, f0, f1, f3⟩ := h₂
    refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂⟩
    simp only [MdStream.Arm.compressK, State.withRegions_gpr,
      State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
      e0, e1, e3, f0, f1, f3, r₁, r₂, and_self]
  · obtain ⟨p, cv, wv⟩ := facts σ s h₁ r₂
    obtain ⟨s₀, hs₀, R, F₀, W, e0, e1, e3⟩ := h₁
    have h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.scrBig
    have fit := gi.scrFit
    have kzp : 0 < kz G.pLen := by simp only [kz]; omega
    have sk4 : 4096 + 640 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega
    have hN := HO.hN; have hso := HO.hso; have hB := HO.hB
    have a0 := h.addr (o := sState) (n := 32) (by simp only [sState]; omega) (by decide)
    have a1 := h.addr (o := sMsg) (n := 64) (by simp only [sMsg]; omega) (by decide)
    have hk : ∀ i ∈ instrs Gh.code, clobbers i .r0 = false ∧ clobbers i .r3 = false := by
      intro i hi
      have := List.all_eq_true.mp HO.callee.keeps i hi
      simpa only [Bool.and_eq_true, Bool.not_eq_true'] using this
    refine VG.Arm.WP.call (k := MdStream.Arm.compressK HO.md) HO.callee.verified p cv wv
      (fun s' hrd hwr hsp hf hg hgc hpost => ?_) HO.callee.noCalls
    have r0' : s'.gpr .r0 = s.gpr .r0 := hgc _ (fun i hi => (hk i hi).1) (by decide)
    simp only [MdStream.Arm.compressK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), e0, e1, r₂, a0, a1] at hpost
    rw [show (1 : BitVec 32).toNat = 1 from rfl, MdStream.Md.compressBlocks_one, HO.iv s.mem _ W] at hpost
    refine ⟨s₀, hs₀, R.mono (by simp) |>.trans (rest_of_preserved hg hrd hwr hsp), ?_, ?_, by rw [r0', e0]⟩
    · refine (F₀.mono (rs' := [G.rs sState (4 * Gh.k), G.rs sA 112]) fun r hr => by
        simp only [List.mem_singleton] at hr; simp [hr]).trans (hf.sub fun r hr => ?_)
      simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState (4 * Gh.k), List.mem_cons_self, by rw [hN]; exact fun _ h => h⟩
      · exact ⟨G.rs sA 112, by simp, by rw [hso]; exact fun _ h => h⟩
    · rw [hpost]
      refine congrArg (HO.md.compress HO.H0) ?_
      unfold VG.Proof.MdStream.Md.blockAt
      refine HO.md.parse_congr fun k hk => ?_
      rw [hB] at hk
      exact F₀.bytes (R := G.rs sMsg 64) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact gi.sdisj (by simp only [sMsg, sState]; omega) (by simp only [sMsg]; omega)
          (by simp only [sState]; have := HO.hk; omega)) (by show 64 ≤ 2 ^ 64; decide) hk
theorem out_length (k : Nat) (f : Nat → BitVec 32) :
    ((List.range k).flatMap fun j => MdStream.bytes32 true (f j)).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton,
      MdStream.bytes32_length]; omega

theorem hash3_vp {F Q : State → State → Prop} {c : State → Cfg} {L dst : Nat} {msg : State → List Byte}
    (hF : ∀ σ s, F σ s → SS G σ (c σ) s) (hL : L = G.pLen)
    (hm : ∀ σ s, F σ s → (msg σ).length < 56 ∧ Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk HO.md (msg σ))
    (hd1 : sState + 32 ≤ dst) (hd2 : dst + 4 * Gh.k ≤ sA)
    (k : ∀ σ s t, F σ s → Rest [.r0, .r1, .r2, .r3, .r6, .r12, .lr] s t →
      Frame [G.rs sState 32, G.rs sA 112, G.rs dst (4 * Gh.k)] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) (4 * Gh.k) = HO.H (msg σ) → Q σ t) :
    VP (H2 HO (G := G) F) (.block (scr L .r6 dst ++ VG.Impl.MdStream.Arm.out32 Gh.k true ++
      [.mov .r9 (.imm (BitVec.ofNat 32 (L / 4)))])) Q := by
  refine VP.taint [.r0, .r8] (HO.cert3 L dst) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · obtain ⟨t₁, f₁, R₁, -, -, e₁⟩ := h₁
    obtain ⟨t₂, f₂, R₂, -, -, e₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [e₁, e₂]
    · rw [R₁.gpr _ (by decide), R₂.gpr _ (by decide), (hF _ _ f₁).r8, (hF _ _ f₂).r8]
  obtain ⟨s₀, hs₀, R, F₀, St, e0⟩ := hs
  have h := hF σ s₀ hs₀
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have hLv := h.lens
  have kzp : 0 < kz G.pLen := by simp only [kz]; omega
  have sk4 : 4096 + 640 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega
  have hk := HO.hk
  have n0 : sState = 64 := rfl
  have n3 : sA = 4096 := rfl
  subst hL
  simp only [List.append_assoc]
  have r8 : s.gpr .r8 = G.KB := by rw [R.gpr _ (by decide), h.r8]
  refine scr_ok (d := .r6) r8 rfl hLv (by omega) fun s₁ v₁ R₁ M₁ => ?_
  have a0 := h.addr (o := sState) (n := 4 * Gh.k) (by omega) (by have := HO.hk0; omega)
  have a6 := h.addr (o := dst) (n := 4 * Gh.k) (by omega) (by have := HO.hk0; omega)
  have t0 := h.toNat (o := sState) (by omega)
  have t6 := h.toNat (o := dst) (by omega)
  have r0₁ : s₁.gpr .r0 = G.scr + BitVec.ofNat 32 sState := by rw [R₁.gpr _ (by decide), e0]
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.MdStream.Arm.out32_ok (n := Gh.k) true (by omega)
    (by rw [r0₁, t0]; omega) (by rw [v₁, t6]; omega)
    (by rw [r0₁, a0, R₁.rd, R₁.wr, R.rd, R.wr]
        obtain ⟨r, hr, hc⟩ := gi.inScr (o := sState) (n := 4 * Gh.k) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [v₁, a6, R₁.wr, R.wr]; exact gi.inScr (by omega))
    (by rw [r0₁, v₁, a0, a6]; exact gi.sdisj (by omega) (by omega) (by omega)))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => wp_mov (op2_imm (by
      rcases hLv with e | e | e <;> rw [e] <;> exact encodable_lt (by decide))) fun t u => WP.block_nil ?_
  rw [r0₁, v₁, a0, a6, M₁] at m₂
  have mt : t.mem = VG.WriteBytes.writeBytes s.mem (G.sa dst) (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) := by
    rw [u.mem, m₂, HO.digest]
  have Rt : Rest [.r0, .r1, .r2, .r3, .r6, .r12, .lr] s₀ t := by
    refine ⟨fun r hr => ?_, by rw [u.rd, rd₂, R₁.rd, R.rd], by rw [u.wr, wr₂, R₁.wr, R.wr],
      by rw [u.sp, sp₂, R₁.sp, R.sp]⟩
    by_cases h9 : r = .r9
    · subst h9; rw [u.gpr, h.r9]
    · rw [u.other r (fun e => h9 (by rw [e])), g₂ r h9, R₁.gpr r (by
          intro hm; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
          rcases hm with rfl | rfl <;> simp),
        R.gpr r (by
          intro hm; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
          rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
  have dl : (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))).length = 4 * Gh.k := by
    rw [HO.digest, out_length]
  refine k σ s₀ t hs₀ Rt ?_ ?_
  · refine (F₀.sub (rs' := [G.rs sState 32, G.rs sA 112, G.rs dst (4 * Gh.k)]) fun r hr => ?_).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState 32, List.mem_cons_self, Region.sub_prefix (by omega)⟩
      · exact ⟨G.rs sA 112, by simp, fun _ h => h⟩
    · rw [mt]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := G.rs dst (4 * Gh.k)) ?_).mono (by simp)
      rw [dl]; exact Region.contains_self _ _
  · obtain ⟨ml, hb⟩ := hm σ s₀ hs₀
    have e := VG.Proof.Sha256.Stream.bytesAt_writeBytes s.mem (G.sa dst) 0
      (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) (by rw [dl]; omega)
    rw [BitVec.add_zero, Nat.zero_add, dl] at e
    show Spec.Sha256.bytesAt _ _ _ = _
    rw [mt, e, St, blockAt_eq HO hb, ← HO.hash _ ml]; rfl

theorem mov2_vp {F : State → State → Prop} :
    VP (H1 (G := G) (Gh := Gh) F) (.block [.mov .r2 (.imm 1)])
      (fun σ s => H1 (G := G) (Gh := Gh) F σ s ∧ s.gpr .r2 = 1) := by
  refine VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs []) (.block [.mov .r2 (.imm 1)]), rfl⟩
    (fun _ _ _ _ _ _ r hr => absurd hr (by simp)) fun σ s ⟨s₀, hs₀, R, F₀, W, e0, e1, e3⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨⟨s₀, hs₀, R.trans (u.rest (by simp)), by rw [u.mem]; exact F₀,
    by rw [u.mem]; exact W, by rw [u.other _ (by decide), e0], by rw [u.other _ (by decide), e1],
    by rw [u.other _ (by decide), e3]⟩, u.gpr⟩

/-- `hash L Gh dst`: the digest of the message whose block is at `sMsg` into `dst`. -/
theorem hash_vp {F Q : State → State → Prop} {c : State → Cfg} {L dst : Nat} {msg : State → List Byte}
    (hF : ∀ σ s, F σ s → SS G σ (c σ) s) (hL : L = G.pLen)
    (hm : ∀ σ s, F σ s → (msg σ).length < 56 ∧ Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk HO.md (msg σ))
    (hd1 : sState + 32 ≤ dst) (hd2 : dst + 4 * Gh.k ≤ sA)
    (k : ∀ σ s t, F σ s → Rest [.r0, .r1, .r2, .r3, .r6, .r12, .lr] s t →
      Frame [G.rs sState 32, G.rs sA 112, G.rs dst (4 * Gh.k)] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) (4 * Gh.k) = HO.H (msg σ) → Q σ t) :
    VP F (hash L Gh dst) Q :=
  VP.seq (hash1_vp HO hF hL) (VP.seq (VP.seq mov2_vp (hash2_vp HO hF)) (hash3_vp HO hF hL hm hd1 hd2 k))

end

end VG.Proof.Dsa.Arm.Gen
