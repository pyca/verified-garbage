module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.Memory
public import VerifiedGarbage.Proof.MdStream.Arm.Common

/-! ### `Dsa.Arm.Gen.Hash`, which this module and modules that import it used -/

section

/-! # DSA parameter generation on ARMv7: a hash of one block

`hash L Gh dst` (`Impl/Dsa/Arm/Generation.lean`) hashes the block at
`sMsg`: the initial hash value into `sState` (`ivStore_ok`), the
compression function on it (`MdStream.Arm.compressAt_ok`), and the hash
value's words big-endian at `dst` (`MdStream.Arm.out32_ok`). `HashOk Gh`
is what the proof needs of the hash function: its compression function
verified, as the streaming proofs see it, and its digest of a message of
fewer than 56 bytes as that compression of its one padded block.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_movw wp_mov wp_dp wp_str op2_reg op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-! ## The initial hash value -/

/-- `ivStore` from word `n` on. -/
def ivAt (iv : List (BitVec 32)) (n : Nat) : List Instr :=
  (iv.zipIdx n).flatMap fun (v, i) => const v ++ [.str .r1 .r0 (4 * i)]

theorem ivStore_eq (iv : List (BitVec 32)) : ivStore iv = ivAt iv 0 := rfl

theorem wp_movt {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (VG.Proof.X25519.Arm.Upd.setReg _ _ _))

theorem ivAt_ok {p : BitVec 32} {R : Region} : ∀ (iv : List (BitVec 32)) (n : Nat) (s : State) (rest : List Instr)
    (Q : State → Prop), s.gpr .r0 = p → 4 * (n + iv.length) ≤ 4096 → p.toNat + 4 * (n + iv.length) ≤ 2 ^ 32 →
    R ∈ s.wr → (∀ j < iv.length, R.Contains (State.addr p + BitVec.ofNat 64 (4 * (n + j))) 4) →
    (∀ t, Rest [.r1] s t → Frame [⟨State.addr p + BitVec.ofNat 64 (4 * n), 4 * iv.length⟩] s.mem t.mem →
      (∀ j (hj : j < iv.length), t.mem.readW (State.addr p + BitVec.ofNat 64 (4 * (n + j))) 32 = iv[j]) →
      WP isa (.block rest) t Q) →
    WP isa (.block (ivAt iv n ++ rest)) s Q
  | [], _, s, _, _, _, _, _, _, _, k => k s (Rest.refl _ _) (Frame.refl _ _) fun _ hj => absurd hj (by simp)
  | v :: vs, n, s, rest, Q, h0, hn, hf, hR, hc, k => by
    simp only [List.length_cons] at hn hf hc
    simp only [ivAt, List.zipIdx_cons, List.flatMap_cons, const, List.cons_append, List.nil_append]
    refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
    have e0 : s₂.gpr .r0 = p := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h0]
    have ea : State.addr (s₂.gpr .r0 + BitVec.ofNat 32 (4 * n)) = State.addr p + BitVec.ofNat 64 (4 * n) := by
      rw [e0]; exact addr_add (by omega_using [hf])
    have hc0 := hc 0 (by omega_using [])
    rw [Nat.add_zero] at hc0
    refine wp_str (by omega_using [hn]) ea ⟨R, by rw [u₂.wr, u₁.wr]; exact hR, hc0⟩ fun s₃ m₃ => ?_
    have v₂ : s₂.gpr .r1 = v := by rw [u₂.gpr, u₁.gpr]; exact VG.Arm.movw_movt v
    refine ivAt_ok vs (n + 1) s₃ rest Q (by rw [m₃.gpr, e0]) (by omega_using [hn]) (by omega_using [hf])
      (by rw [m₃.wr, u₂.wr, u₁.wr]; exact hR)
      (fun j hj => by rw [show n + 1 + j = n + (j + 1) by omega_using []]; exact hc (j + 1) (by omega_using [hj]))
      fun t R' F' W' => ?_
    have base : Region.Sub ⟨State.addr p + BitVec.ofNat 64 (4 * (n + 1)), 4 * vs.length⟩
        ⟨State.addr p + BitVec.ofNat 64 (4 * n), 4 * (vs.length + 1)⟩ := by
      rw [show 4 * (n + 1) = 4 * n + 4 by omega_using [], ← Offset.add_add]
      exact Offset.sub_base _ (by omega_using [])
    refine k t (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((m₃.rest _).trans R')) ?_ fun j hj => ?_
    · have f₃ : Frame [⟨State.addr p + BitVec.ofNat 64 (4 * n), 4 * (vs.length + 1)⟩] s.mem s₃.mem := by
        rw [m₃.mem, u₂.mem, u₁.mem]
        refine Frame.writeW (Frame.refl _ s.mem) List.mem_cons_self (w := 32) (s₂.gpr .r1) ?_
        show (_ - _ : Addr).toNat + 4 ≤ _
        rw [BitVec.sub_self, BitVec.toNat_zero]; show 0 + 4 ≤ 4 * (vs.length + 1); omega_using []
      exact f₃.trans (F'.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, base⟩)
    · cases j with
      | zero =>
        rw [Nat.add_zero]
        have d : Region.Disjoint ⟨State.addr p + BitVec.ofNat 64 (4 * n), 4⟩
            ⟨State.addr p + BitVec.ofNat 64 (4 * (n + 1)), 4 * vs.length⟩ := by
          rw [show 4 * (n + 1) = 4 * n + 4 by omega_using [], ← Offset.add_add]
          exact (Offset.disjoint_base _ (Nat.le_refl 4) (by omega_using [hn])).symm
        rw [F'.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact d) (by decide), m₃.mem, Mem.readW_writeW_self32, v₂]
        rfl
      | succ j =>
        have := W' j (by simp at hj; omega_using [hj])
        rw [show n + (j + 1) = n + 1 + j by omega_using []]
        exact this

/-! ## What the proof needs of the hash function -/

/-- The block of a message of fewer than 56 bytes. -/
def blk {B N L : Nat} (md : MdStream.Md B N L) (msg : List Byte) : List Byte :=
  msg ++ [0x80] ++ List.replicate (55 - msg.length) 0 ++ md.lenBytes msg.length

structure HashOk (Gh : Hash) where
  P : VG.Impl.MdStream.Arm.Params
  md : MdStream.Md P.B P.N P.L
  hB : P.B = 64
  hL : P.L = 8
  hN : P.N = 4 * Gh.k
  hso : P.so = 112
  hk : Gh.k ≤ 8
  hk0 : 0 < Gh.k
  ivLen : Gh.iv.length = Gh.k
  callee : MdStream.Arm.CalleeOk md Gh.code
  ct : ConstantTime isa (MdStream.Arm.compressK md).pre (MdStream.Arm.compressK md).pub Gh.code
  /-- The initial hash value. -/
  H0 : md.HV
  iv : ∀ (m : Mem) (p : Addr), (∀ j (hj : j < Gh.iv.length), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = Gh.iv[j]) →
    md.stateAt m p = H0
  digest : ∀ (m : Mem) (p : Addr), md.digest (md.stateAt m p) =
    (List.range Gh.k).flatMap fun j => MdStream.bytes32 true (m.readW (p + BitVec.ofNat 64 (4 * j)) 32)
  /-- The hash function. -/
  H : List Byte → List Byte
  hash : ∀ msg, msg.length < 56 → H msg = md.digest (md.compress H0 (md.parse fun t => (blk md msg).getD t 0))
  /-- The taint analysis of the code before and after the call, which
  depends on the hash function only through its initial hash value and its
  words: checked on each instance. -/
  cert1 : ∀ L, Cert8 (.block (scr L .r0 sState ++ ivStore Gh.iv ++ scr L .r1 sMsg ++ scr L .r3 sA))
  cert3 : ∀ L dst, ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r8]) (.block (scr L .r6 dst ++
      VG.Impl.MdStream.Arm.out32 Gh.k true ++ [.mov .r9 (.imm (BitVec.ofNat 32 (L / 4)))])) hc).isSome = true

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Gen.HashVP`, which only this module used -/

section

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
  obtain h := hF σ s hs
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have hLv := h.lens
  have hk := HO.hk
  have il := HO.ivLen
  subst hL
  simp only [List.append_assoc]
  refine scr_ok (d := .r0) h.r8 rfl hLv (by simp only [sK, sA, wa, sState]; omega_arith) fun s₁ v₁ R₁ M₁ => ?_
  rw [ivStore_eq]
  obtain e₀ : State.addr (G.scr + BitVec.ofNat 32 sState) = G.sa sState := h.addr (n := 32)
    (by simp only [sK, sA, wa, sState]; omega_arith) (by decide)
  obtain tn := h.toNat (o := sState) (by simp only [sK, sA, wa, sState]; omega_arith)
  have e64 : sState = 64 := rfl
  obtain kzp : 0 < kz G.pLen := by simp only [kz]; omega_arith
  obtain sk4 : 4096 ≤ sK G.pLen := by simp only [sK, sA]; omega_arith
  refine ivAt_ok (R := G.rScr) Gh.iv 0 s₁ _ _ v₁ (by omega_arith) (by rw [tn]; omega_arith)
    (by rw [R₁.wr, gi.wr, gi.pre.wr, gi.hG]; simp) (fun j hj => ?_) fun s₂ R₂ F₂ W₂ => ?_
  · rw [e₀, Nat.zero_add, Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain r8₂ : s₂.gpr .r8 = G.KB := by rw [R₂.gpr _ (by decide), R₁.gpr _ (by decide), h.r8]
  refine scr_ok (d := .r1) r8₂ rfl hLv (by simp only [sK, sA, wa, sMsg]; omega_arith) fun s₃ v₃ R₃ M₃ => ?_
  refine scr_ok (d := .r3) (by rw [R₃.gpr _ (by decide), r8₂]) rfl hLv (by simp only [sK, sA, wa]; omega_arith)
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
  ⟨fun r hr => g r (by revert hr; cases r <;> decide) (by rintro rfl; simp at hr), rd, wr, sp⟩

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
  obtain facts : ∀ σ s, H1 (G := G) (Gh := Gh) F σ s → s.gpr .r2 = 1 →
      (MdStream.Arm.compressK HO.md).pre (s.callEntry.withRegions rd wr) ∧ Covers (rd ++ wr) (s.rd ++ s.wr) ∧
        Covers wr s.wr := by
    intro σ s ⟨s₀, hs₀, R, _, _, e0, e1, e3⟩ e2
    obtain h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.scrBig
    have fit := gi.scrFit
    obtain kzp : 0 < kz G.pLen := by simp only [kz]; omega_arith
    obtain sk4 : 4096 + 640 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega_arith
    obtain hB := HO.hB; have hN := HO.hN; have hso := HO.hso; have hk := HO.hk
    obtain a0 := h.addr (o := sState) (n := 32) (by simp only [sState]; omega_arith) (by decide)
    obtain a1 := h.addr (o := sMsg) (n := 64) (by simp only [sMsg]; omega_arith) (by decide)
    obtain a3 := h.addr (o := sA) (n := 112) (by simp only [sA]; omega_arith) (by decide)
    obtain t0 := h.toNat (o := sState) (by simp only [sState]; omega_arith)
    obtain t1 := h.toNat (o := sMsg) (by simp only [sMsg]; omega_arith)
    obtain t3 := h.toNat (o := sA) (by simp only [sA]; omega_arith)
    have ws : s.wr = s₀.wr := R.wr
    have rds : s.rd = s₀.rd := R.rd
    obtain hw : Covers wr s.wr := by
      rw [ws]
      refine Covers.pair (Covers.one (gi.inScr ?_)) (Covers.one (gi.inScr ?_)) <;>
        simp only [sState, sA, hN, hso] <;> omega_arith
    refine ⟨?_, Covers.append_left (Covers.right (Covers.one (by
      rw [ws]; exact gi.inScr (by simp only [sMsg, hB]; omega_arith)))) hw.right, hw⟩
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
      ?_, ?_, ?_⟩ <;> omega_arith
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
    obtain h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.scrBig
    have fit := gi.scrFit
    obtain kzp : 0 < kz G.pLen := by simp only [kz]; omega_arith
    obtain sk4 : 4096 + 640 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega_arith
    obtain hN := HO.hN; have hso := HO.hso; have hB := HO.hB
    obtain a0 := h.addr (o := sState) (n := 32) (by simp only [sState]; omega_arith) (by decide)
    obtain a1 := h.addr (o := sMsg) (n := 64) (by simp only [sMsg]; omega_arith) (by decide)
    obtain hk : ∀ i ∈ instrs Gh.code, clobbers i .r0 = false ∧ clobbers i .r3 = false := by
      intro i hi
      have := List.all_eq_true.mp HO.callee.keeps i hi
      simpa only [Bool.and_eq_true, Bool.not_eq_true'] using this
    refine VG.Arm.WP.call (k := MdStream.Arm.compressK HO.md) HO.callee.verified p cv wv
      (fun s' hrd hwr hsp hf hg hgc hpost => ?_) HO.callee.noCalls
    obtain r0' : s'.gpr .r0 = s.gpr .r0 := hgc _ (fun i hi => (hk i hi).1) (by decide)
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
        exact gi.sdisj (by simp only [sMsg, sState]; omega_arith) (by simp only [sMsg]; omega_arith)
          (by simp only [sState]; have := HO.hk; omega_arith)) (by show 64 ≤ 2 ^ 64; decide) hk
theorem out_length (k : Nat) (f : Nat → BitVec 32) :
    ((List.range k).flatMap fun j => MdStream.bytes32 true (f j)).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton,
      MdStream.bytes32_length]; omega_arith

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
  obtain h := hF σ s₀ hs₀
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have hLv := h.lens
  obtain kzp : 0 < kz G.pLen := by simp only [kz]; omega_arith
  obtain sk4 : 4096 + 640 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega_arith
  have hk := HO.hk
  have n0 : sState = 64 := rfl
  have n3 : sA = 4096 := rfl
  subst hL
  simp only [List.append_assoc]
  obtain r8 : s.gpr .r8 = G.KB := by rw [R.gpr _ (by decide), h.r8]
  refine scr_ok (d := .r6) r8 rfl hLv (by omega_arith) fun s₁ v₁ R₁ M₁ => ?_
  obtain a0 := h.addr (o := sState) (n := 4 * Gh.k) (by omega_arith) (by have := HO.hk0; omega_arith)
  obtain a6 := h.addr (o := dst) (n := 4 * Gh.k) (by omega_arith) (by have := HO.hk0; omega_arith)
  obtain t0 := h.toNat (o := sState) (by omega_arith)
  obtain t6 := h.toNat (o := dst) (by omega_arith)
  obtain r0₁ : s₁.gpr .r0 = G.scr + BitVec.ofNat 32 sState := by rw [R₁.gpr _ (by decide), e0]
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.MdStream.Arm.out32_ok (n := Gh.k) true (by omega_arith)
    (by rw [r0₁, t0]; omega_arith) (by rw [v₁, t6]; omega_arith)
    (by rw [r0₁, a0, R₁.rd, R₁.wr, R.rd, R.wr]
        obtain ⟨r, hr, hc⟩ := gi.inScr (o := sState) (n := 4 * Gh.k) (by omega_arith)
        exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [v₁, a6, R₁.wr, R.wr]; exact gi.inScr (by omega_arith))
    (by rw [r0₁, v₁, a0, a6]; exact gi.sdisj (by omega_arith) (by omega_arith) (by omega_arith)))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => wp_mov (op2_imm (by
      rcases hLv with e | e | e <;> rw [e] <;> exact encodable_lt (by decide))) fun t u => WP.block_nil ?_
  rw [r0₁, v₁, a0, a6, M₁] at m₂
  obtain mt : t.mem = VG.WriteBytes.writeBytes s.mem (G.sa dst) (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) := by
    rw [u.mem, m₂, HO.digest]
  obtain Rt : Rest [.r0, .r1, .r2, .r3, .r6, .r12, .lr] s₀ t := by
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
  obtain dl : (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))).length = 4 * Gh.k := by
    rw [HO.digest, out_length]
  refine k σ s₀ t hs₀ Rt ?_ ?_
  · refine (F₀.sub (rs' := [G.rs sState 32, G.rs sA 112, G.rs dst (4 * Gh.k)]) fun r hr => ?_).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState 32, List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
      · exact ⟨G.rs sA 112, by simp, fun _ h => h⟩
    · rw [mt]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := G.rs dst (4 * Gh.k)) ?_).mono (by simp)
      rw [dl]; exact Region.contains_self _ _
  · obtain ⟨ml, hb⟩ := hm σ s₀ hs₀
    obtain e := VG.Proof.Sha256.Stream.bytesAt_writeBytes s.mem (G.sa dst) 0
      (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) (by rw [dl]; omega_arith)
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

end

end

/-! ### `Dsa.Arm.Gen.QShape`, which only this module used -/

section

/-! # DSA parameter generation on ARMv7: q's top and low bits

The block after q's hash sets the top bit of its first byte and the low bit
of its last (`shapeQ_vp`): the bytes become `shapedOctets digest 7`, whose
value is `qCandidate` (`Proof.Dsa.Generation.qShape_memory`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_dp wp_ldrb wp_strb op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The bit operations of the block. -/
abbrev shapeOps (N : Nat) : List Instr :=
  [.ldrb .r1 .r0 0, .dp .orr .r1 .r1 (.imm 0x80), .strb .r1 .r0 0,
    .ldrb .r1 .r0 (N - 1), .dp .orr .r1 .r1 (.imm 1), .strb .r1 .r0 (N - 1)]

theorem orr_byte (b : Byte) (x : BitVec 32) :
    (b.setWidth 32 ||| x).setWidth 8 = b ||| x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or]
  simp [hi, show i < 32 by omega_using [hi]]

section
variable {G : GP}

theorem shapeQ_vp {P Q : State → State → Prop} {c : State → Cfg} {L N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G σ (c σ) s) (hL : L = G.pLen) (hN : 2 ≤ N) (hN' : N ≤ 32)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sQ) N = bs)
    (k : ∀ σ s t, P σ s → Rest [.r0, .r1, .r12] s t → Frame [G.rs sQ N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sQ) N = VG.Proof.Ffdh.ParameterCandidate.shapedOctets bs 7 → Q σ t) :
    VP P (.block (scr L .r0 sQ ++ shapeOps N)) Q := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sQ ++ shapeOps 20)), rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).r8, (hF _ _ h₂).r8]
  obtain h := hF σ s hs
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  obtain sk : 4096 ≤ sK G.pLen := by simp only [sK, sA]; omega_using []
  have nq : sQ = 128 := rfl
  obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_using []
  subst hL
  refine scr_ok (d := .r0) h.r8 rfl h.lens (by omega_using [sk, nq]) fun s₁ v₁ R₁ M₁ => ?_
  obtain aq := h.addr (o := sQ) (n := N) (by omega_using [hN', sk, nq]) (by omega_using [hN])
  obtain w : ∀ j < N, InRegions s.wr (G.sa sQ + BitVec.ofNat 64 j) 1 := fun j hj =>
    Covers.one (gi.inScr (o := sQ) (n := N) (by omega_using [hN', big, sk, nq])) _ _
      ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hN', hj])⟩
  obtain r_of : ∀ j < N, InRegions (s.rd ++ s.wr) (G.sa sQ + BitVec.ofNat 64 j) 1 := fun j hj =>
    let ⟨r, hr, hc⟩ := w j hj; ⟨r, List.mem_append_right _ hr, hc⟩
  obtain a0 : State.addr (s₁.gpr .r0 + BitVec.ofNat 32 0) = G.sa sQ := by rw [BitVec.add_zero, v₁, aq]
  obtain aN : State.addr (s₁.gpr .r0 + BitVec.ofNat 32 (N - 1)) = G.sa sQ + BitVec.ofNat 64 (N - 1) := by
    rw [v₁, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega_using [hN', big, fit, sk, nq]), Offset.add_add]
  simp only [shapeOps]
  refine wp_ldrb (by decide) a0 (by rw [R₁.rd, R₁.wr]; simpa using r_of 0 (by omega_using [hN])) fun s₂ u₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_strb (a := G.sa sQ) (by decide) (by rw [u₃.other .r0 (by decide), u₂.other .r0 (by decide)]; exact a0)
    (by rw [u₃.wr, u₂.wr, R₁.wr]; simpa using w 0 (by omega_using [hN])) fun s₄ u₄ => ?_
  obtain a4 : State.addr (s₄.gpr .r0 + BitVec.ofNat 32 (N - 1)) = G.sa sQ + BitVec.ofNat 64 (N - 1) := by
    rw [u₄.gpr, u₃.other .r0 (by decide), u₂.other .r0 (by decide)]; exact aN
  refine wp_ldrb (by omega_using [hN']) a4 (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, R₁.rd, R₁.wr]; exact r_of _ (by omega_using [hN]))
    fun s₅ u₅ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₆ u₆ => ?_
  refine wp_strb (a := G.sa sQ + BitVec.ofNat 64 (N - 1)) (by omega_using [hN'])
    (by rw [u₆.other .r0 (by decide), u₅.other .r0 (by decide)]; exact a4)
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, R₁.wr]; exact w _ (by omega_using [hN])) fun t u₇ => WP.block_nil ?_
  obtain R : Rest [.r0, .r1, .r12] s t := ((R₁.mono (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))).trans
    ((u₄.rest _).trans ((u₅.rest (by simp)).trans ((u₆.rest (by simp)).trans (u₇.rest _))))
  obtain m₄ : s₄.mem = s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8) := by
    rw [u₄.mem, u₃.mem, u₂.mem, M₁, u₃.gpr, dpVal, u₂.gpr, M₁, orr_byte]; rfl
  obtain b₄ : s₄.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) = s.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) := by
    rw [m₄, VG.WriteBytes.writeW8_apply, ite_eq_right (by
      have := Offset.add_ofNat_ne (G.sa sQ) (a := N - 1) (b := 0) (by omega_using [hN']) (by omega_using []) (by omega_using [hN])
      simpa using this)]
  obtain mt : t.mem = (s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8)).writeW
      (G.sa sQ + BitVec.ofNat 64 (N - 1)) (s.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) ||| 1#8) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₆.gpr, dpVal, u₅.gpr, b₄, orr_byte, ← m₄]; rfl
  obtain hb' := hb σ s hs
  obtain bl : bs.length = N := by rw [← hb', bytesAt_length']
  refine k σ s t hs R ?_ ?_
  · rw [mt]
    obtain c0 : (G.rs sQ N).Contains (G.sa sQ) (8 / 8) := by
      show (_ - _ : Addr).toNat + 1 ≤ N
      rw [BitVec.sub_self, BitVec.toNat_zero]; omega_using [hN]
    exact ((Frame.refl [G.rs sQ N] s.mem).writeW List.mem_cons_self (w := 8) _ c0).writeW List.mem_cons_self
      (w := 8) _ (Offset.contains_base _ (by omega_using [hN]) (by omega_using [hN']))
  · rw [mt, ← bl]
    refine VG.Proof.Dsa.Generation.qShape_memory (by omega_using [hN, bl]) (by omega_using [hN', bl]) fun i hi => ?_
    rw [← hb']
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, bl ▸ hi]

end

end VG.Proof.Dsa.Arm.Gen

end

end


/-! # DSA parameter generation on ARMv7: q

`qPart` (`qPart_vp`): the seed at `fSeed` copied before the block's padding
at `sMsg`, hashed into `sQ`, its top and low bits set, copied to `sA` and
tested. The claims after it: the padding, and q's bytes at `sQ`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Ffdh.ParameterCandidate (shapedOctets)

/-- The seed at byte `k` of the tape. -/
abbrev seedAt (G : GP) (k : Nat) : List Byte := (G.seedsB.drop k).take G.qLen

/-- The block after a message of `n` bytes. -/
def padTail {B N L : Nat} (md : MdStream.Md B N L) (n : Nat) : List Byte :=
  [0x80] ++ List.replicate (55 - n) 0 ++ md.lenBytes n

/-- q's bytes, from the seed at `k`. -/
abbrev qBytes (G : GP) (k : Nat) : List Byte :=
  shapedOctets (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)) 7

/-- The claims after q: the padding, and q's bytes at `sQ`. -/
abbrev qClaims {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat}

theorem GI.seedsFit (h : GI G σ V LS s) : G.seeds.toNat + G.seedsLen ≤ 2 ^ 32 := by
  have := h.pre.nW; rw [← h.hG]; exact this

/-- The seed at `k`, in memory. -/
theorem GI.seedBytes (h : GI G σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.seedsLen) :
    Spec.Rsa.bytesAt s.mem (State.addr (G.seeds + BitVec.ofNat 32 k)) G.qLen = seedAt G k := by
  obtain e : G.seedsB = Spec.Rsa.bytesAt σ.mem (State.addr G.seeds) G.seedsLen := by rw [← h.hG]; rfl
  rw [h.keeps h.seedsFit h.seeds_apart hk, seedAt, e]

/-- The seed at `k`, as a source of a copy. -/
theorem GI.seedSrc (h : GI G σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hq : 0 < G.qLen) :
    InRegions s.rd (State.addr (G.seeds + BitVec.ofNat 32 k)) G.qLen ∧
      Region.Disjoint ⟨State.addr (G.seeds + BitVec.ofNat 32 k), G.qLen⟩ G.rScr ∧
      (G.seeds + BitVec.ofNat 32 k).toNat + G.qLen ≤ 2 ^ 32 := by
  have fit := h.seedsFit
  obtain a : State.addr (G.seeds + BitVec.ofNat 32 k) = State.addr G.seeds + BitVec.ofNat 64 k := addr_add (by omega_arith)
  obtain sub : Region.Sub ⟨State.addr G.seeds + BitVec.ofNat 64 k, G.qLen⟩ G.rSeeds := Offset.sub_base _ hk
  obtain sC := h.pre.wC; rw [h.hG] at sC
  refine ⟨⟨G.rSeeds, ?_, a ▸ Offset.contains_base _ hk (by omega_arith)⟩, a ▸ sC.sub_left sub, ?_⟩
  · rw [h.rd, h.pre.rd, h.hG]; simp
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

end

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem padTail_length {B N L : Nat} (md : MdStream.Md B N L) {n : Nat} (hn : n < 56) (hL : L = 8) :
    (padTail md n).length = 64 - n := by
  simp only [padTail, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    md.lenBytes_length]
  omega_arith

/-- The seed at `k` (at `fSeed`) to `sMsg`. -/
theorem seedCopy_vp {L k : Nat} (hL : L = G.pLen) (hk : k + G.qLen ≤ G.seedsLen) (hq0 : 0 < G.qLen)
    (hq16 : G.qLen < 2 ^ 16) (hqK : G.qLen ≤ sK G.pLen) (hsb : G.seedsB.length = G.seedsLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg G.qLen x) :
    VP (St G c X) (copyN (scr L .r0 sMsg) [ld .r1 fSeed] G.qLen)
      (St G { c with cl := (sMsg, seedAt G k) :: cl' } X) := by
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  refine copyR_vp (c := fun _ => c) (fun σ s h => h.1) hL (by decide) (by decide)
    (x := G.seeds + BitVec.ofNat 32 k) (fun σ s h => (h.1.slotV hS).trans hSv) hq0 hq16
    (by subst hL; simp only [sMsg]; omega_arith) (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
  rw [h.gi.seedBytes hk] at e
  refine h.of_scr R (o := sMsg) (n := G.qLen) (by simp only [sMsg]; omega_arith) (f.mono (by simp)) fun y hy => ?_
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [hsl]; exact e, by simp only [sMsg, hsl]; omega_arith⟩
  · exact .inl (hcl y hy)

/-- q from the seed at `k`, tested with the witnesses from `u`. -/
theorem qPart_vp {g : Geo} (HO : HashOk g.G) (ok : PrimeOk (8 * G.qLen) g.qCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsb : G.seedsB.length = G.seedsLen)
    (hsize : keyOff + 8 * keyWords (8 * G.qLen) ≤ wa G.pLen) (hb8 : 8 * G.qLen / 8 ≤ wa G.pLen)
    {k u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 32 u) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS)
    (hpad : (G.qLen, padTail HO.md G.qLen) ∈ c.cl) :
    VP (St G c X) g.qPart
      (St G (testCfg c (qClaims HO.md G k) G.witLen
        (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.witB.drop u))) X) := by
  obtain hq0 : 0 < G.qLen := by omega_arith
  obtain hq56 : G.qLen < 56 := by omega_arith
  obtain pl : (padTail HO.md G.qLen).length = 64 - G.qLen := padTail_length HO.md hq56 HO.hL
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  -- The hash and q.
  obtain hHl : (HO.H (seedAt G k)).length = G.qLen := by
    rw [HO.hash _ (by omega_arith), HO.md.digest_length, HO.hN, hk4]
  obtain hne : HO.H (seedAt G k) ≠ [] := fun e => by rw [e] at hHl; simp at hHl; omega_arith
  obtain qb : shapedOctets (HO.H (seedAt G k)) 7 = qBytes G k := by rw [hH]
  obtain qbl : (qBytes G k).length = G.qLen := by
    rw [← qb, shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHl]
  obtain hqc : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [← hH, hHl])
  rw [← hqc]
  obtain hsK : 4096 + 17024 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega_arith
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  generalize hsd : seedAt G k = sd at hsl hHl hne qb
  let c1 : Cfg := { c with cl := [(sMsg, sd), (G.qLen, pad)] }
  let c2 : Cfg := { c with cl := [(G.qLen, pad), (sQ, HO.H sd)] }
  let c3 : Cfg := { c with cl := [(G.qLen, pad), (sQ, qBytes G k)] }
  let c4 : Cfg := { c with cl := [(sA, qBytes G k), (G.qLen, pad), (sQ, qBytes G k)] }
  unfold Geo.qPart
  rw [hq, hp]
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ (VP.seq (G := St G c3 X) ?_
    (VP.seq (G := St G c4 X) ?_ ?_)))
  · -- The seed, before the padding.
    have := seedCopy_vp (X := X) (cl' := [(G.qLen, pad)]) rfl hk hq0 (by omega_arith) (by omega_arith) hsb hS hSv fun y hy => by
      rw [List.mem_singleton] at hy; subst hy; exact ⟨hpad, .inr (by simp only [sMsg]; omega_arith)⟩
    rwa [hsd] at this
  · -- The hash.
    refine hash_vp HO (c := fun _ => c1) (fun σ s h => h.1) rfl (msg := fun _ => sd) (dst := sQ)
      (fun σ s ⟨h, _⟩ => ⟨by omega_arith, ?_⟩) (by decide) (by simp only [sQ, sA]; omega_arith)
      fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
    · have b1 := h.sb (sMsg, sd) (by simp [c1])
      obtain b2 := h.sb (G.qLen, pad) (by simp [c1])
      rw [show (64 : Nat) = sd.length + pad.length by omega_arith, VG.Proof.Dsa.Generation.bytesAt_append, b1]
      obtain a : VG.Proof.Bignum.off (G.sa sMsg) sd.length = G.sa G.qLen := by
        simp only [VG.Proof.Bignum.off, GP.sa, sMsg, hsl]; rw [BitVec.add_zero]
      rw [a, b2, ← hpd]
      simp only [blk, padTail, hsl, List.append_assoc]
    refine h.of_scrs R (os := [(sState, 32), (sA, 112), (sQ, 4 * g.G.k)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ (by simpa [GP.rss] using hr)) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [sState, sA, sQ] <;> omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c1], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl, sState, sA, sQ] <;> omega_arith
    · exact .inr ⟨by rw [hHl, ← hk4]; exact e, by simp only [hHl, sQ]; omega_arith⟩
  · -- q's shape.
    refine shapeQ_vp (c := fun _ => c2) (fun σ s h => h.1) rfl (N := G.qLen) (by omega_arith) (by omega_arith)
      (bs := HO.H sd) (fun σ s ⟨h, _⟩ => by have := h.sb (sQ, HO.H sd) (by simp [c2]); rwa [hHl] at this)
      fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
    refine h.of_scr R (o := sQ) (n := G.qLen) (by simp only [sQ]; omega_arith) (f.mono (by simp)) fun y hy => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact .inl ⟨by simp [c2], .inl (by simp only [pl, sQ]; omega_arith)⟩
    · exact .inr ⟨by rw [qbl, ← qb]; exact e, by simp only [qbl, sQ]; omega_arith⟩
  · -- q to the test's working space.
    refine copyS_vp (c := fun _ => c3) (fun σ s h => h.1) rfl (dst := sA) (src := sQ) (n := G.qLen) hq0
      (by omega_arith) (by simp only [sA]; omega_arith) (by simp only [sQ]; omega_arith) (.inr (by simp only [sQ, sA]; omega_arith))
      fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
    obtain b := h.sb (sQ, qBytes G k) (by simp [c3])
    refine h.of_scr R (o := sA) (n := G.qLen) (by simp only [sA]; omega_arith) (f.mono (by simp)) fun y hy => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact .inr ⟨by rw [qbl, e, ← qbl]; exact b, by simp only [qbl, sA]; omega_arith⟩
    · exact .inl ⟨by simp [c3], .inl (by simp only [pl, sA]; omega_arith)⟩
    · exact .inl ⟨by simp [c3], .inl (by simp only [qbl, sQ, sA]; omega_arith)⟩
  · -- The test.
    obtain hqk := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)
    obtain hbl := VG.Proof.Dsa.Generation.qCandidate_bitLength (n := 8 * G.qLen) (by omega_arith) (seedAt G k)
    rw [← hqc] at hqk hbl
    refine test_vp (c := c4) ok rfl hu hU hUv hwl hsize hb8 (by simp [c4]) (by rw [qbl]; omega_arith) hqk.1 hbl h88 h92
      fun y hy => ?_
    simp only [qClaims, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨by simp [c4, hpd], .inl (by simp only [hpd, pl, sA]; omega_arith)⟩
    · exact ⟨by simp [c4], .inl (by simp only [qbl, sQ, sA]; omega_arith)⟩

end

end VG.Proof.Dsa.Arm.Gen
