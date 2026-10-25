module

import VerifiedGarbage.Proof.Ffdh.AArch64.Front
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN
public import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Front
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# FFDH on AArch64: the front in constant time

The check of p (`domHead_ct`) and the workspaces with p, `-p⁻¹` and the
number 1 (`setup_ct`) leak the same in runs with the same working space,
domain pointer and p's length (`DPub`), whatever p: between the pieces,
each run satisfies a stage (`SP1` … `SP3`, `SWPre`) by their correctness,
and the registers a piece's addresses and loop counts come from are fixed
by the stage.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (wsEnd wsNew loadArr leave ldw)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- The public data of the front: the working space, p's length and the
domain's pointer. -/
structure DPub where
  B : Addr
  Z : Nat
  k : Nat
  dp : Addr

/-- The words of p. -/
abbrev DPub.w (a : DPub) : Nat := (a.k + 7) / 8

/-- The inner workspace, as the arithmetic sees it. -/
abbrev DPub.ws (a : DPub) : Ws := ⟨off a.B (inner a.w), slot a.w 8, a.w⟩

/-- p's load. -/
abbrev DPub.bp (a : DPub) : BPub := ⟨⟨a.B, a.Z, inner a.w, a.w, a.w⟩, a.dp, a.k⟩

/-! ## The check of p -/

/-- `domHead_ok`'s hypotheses. -/
def DHP (a : DPub) (s : State) : Prop :=
  Scr s a.B a.Z ∧ s.gpr .x0 = a.B ∧ 256 ≤ a.Z ∧ word s.mem a.B (8 * sDom) = a.dp ∧
    word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.k

theorem domHead_ct : RelCT isa (Two DHP) (.block domHead) fun _ _ => True := by
  unfold domHead
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (a : DPub) t => t.gpr .x2 = a.dp ∧
      t.gpr .x3 = BitVec.ofNat 64 a.k) [.x0] (pins_x0B DPub.B fun _ _ h => h.2.1) (by taint_decide)
      fun a s h => ?_)
    (two_taint [.x2, .x3] (pins_of (fun (a : DPub) r => if r = .x2 then a.dp else BitVec.ofNat 64 a.k)
      fun a s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide)))
  obtain ⟨hs, h0, hZ, hD, hK⟩ := h
  exact WP.mono (domHead1_ok hs h0 hZ hD hK) fun t ⟨⟨h2, h3, _⟩, _⟩ => ⟨h2, h3⟩

/-! ## The workspaces -/

/-- `setup_ok`'s hypotheses. -/
def SetupP (a : DPub) (s : State) : Prop :=
  ∃ pb : List Byte, Scr s a.B a.Z ∧ s.gpr .x0 = a.B ∧ 64 ≤ a.k ∧ a.k ≤ 1024 ∧ 128 * a.k + 256 ≤ a.Z ∧
    word s.mem a.B (8 * sDom) = a.dp ∧ word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.k ∧ Src s a.B a.Z a.dp pb ∧
    pb.length = a.k ∧ Spec.Rsa.os2ip pb % 2 = 1

/-- After `head`: the outer workspace. -/
def SP1 (a : DPub) (s : State) : Prop :=
  ∃ pb : List Byte, Outer s a.B a.Z a.w ∧ 64 ≤ a.k ∧ a.k ≤ 1024 ∧ 128 * a.k + 256 ≤ a.Z ∧
    word s.mem a.B (8 * sDom) = a.dp ∧ word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.k ∧ Src s a.B a.Z a.dp pb ∧
    pb.length = a.k ∧ Spec.Rsa.os2ip pb % 2 = 1

/-- The public data of a modulus' workspace: the outer workspace of `w`
words, and the modulus' length and pointer. -/
structure MPub where
  B : Addr
  Z : Nat
  w : Nat
  len : Nat
  ptr : Addr

abbrev MPub.wx (a : MPub) : Nat := wsWords a.len

/-- The inner workspace, as the arithmetic sees it. -/
abbrev MPub.ws (a : MPub) : Ws := ⟨off a.B (inner a.w), slot a.wx 8, a.wx⟩

/-- The modulus' load. -/
abbrev MPub.bp (a : MPub) : BPub := ⟨⟨a.B, a.Z, inner a.w, a.w, a.wx⟩, a.ptr, a.len⟩

/-- `wsMod_ok`'s hypotheses: the outer workspace, and the modulus' length and
pointer in its slots `sl` and `sp`. -/
def M1 (sp sl : Nat) (a : MPub) (s : State) : Prop :=
  ∃ bs : List Byte, Outer s a.B a.Z a.w ∧ word s.mem a.B (8 * sl) = BitVec.ofNat 64 a.len ∧
    word s.mem a.B (8 * sp) = a.ptr ∧ Src s a.B a.Z a.ptr bs ∧ bs.length = a.len ∧ 1 ≤ a.len ∧
    a.len ≤ 8 * a.w ∧ Spec.Rsa.os2ip bs % 2 = 1

/-- In the inner workspace. -/
def M2 (sp sl : Nat) (a : MPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (bs : List Byte), SubCtx s a.B a.Z (inner a.w) a.w a.wx mi ∧
    word s.mem a.B (8 * sl) = BitVec.ofNat 64 a.len ∧ word s.mem a.B (8 * sp) = a.ptr ∧ Src s a.B a.Z a.ptr bs ∧
    bs.length = a.len ∧ 1 ≤ a.len ∧ a.len ≤ 8 * a.w ∧ Spec.Rsa.os2ip bs % 2 = 1 ∧ 2 ≤ a.w ∧ a.w < 2 ^ 28

/-- With the modulus, odd, in `aN`. -/
def M3 (a : MPub) (s : State) : Prop :=
  ∃ mi : BitVec 64, SubCtx s a.B a.Z (inner a.w) a.w a.wx mi ∧
    (word s.mem (off a.B (inner a.w)) (slot a.wx aN)).toNat % 2 = 1

theorem m1_pin (sp sl : Nat) (a : MPub) (s : State) (h : M1 sp sl a s) :
    WP isa (.block ([mov .x5 .x0] ++ wsEnd)) s fun t => t.gpr .x0 = a.B ∧ t.gpr .x4 = off a.B (inner a.w) := by
  obtain ⟨_, hO, -⟩ := h
  have hroom := hO.room
  have hw28 := hO.w28
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = a.B ∧ t.mem = s.mem) (by brun [hO.x0]) (by decide)
    (by decide) (by decide +kernel)) fun s₁ ⟨⟨h5₁, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (wsEnd_ok (wx := a.w) (hO.scr.congr k₁.wr) h5₁ (by rw [hm₁]; exact hO.hw) (by omega_arith)
    (by rw [hm₁]; exact hO.harr _ (by decide)) (by unfold inner tabBytes32 at hroom; omega_arith))
    fun t ⟨⟨h4, _, _⟩, k₂⟩ => ⟨(k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans hO.x0), h4⟩

theorem m1_m2 {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (hspW : sp ≠ sWs) (hslW : sl ≠ sWs) (a : MPub)
    (s : State) (h : M1 sp sl a s) : WP isa (.block (wsSetup sl ++ [enter])) s (M2 sp sl a) := by
  obtain ⟨bs, hO, hL, hP, hsrc, hl, h1, hlw, hodd⟩ := h
  have hn := hO.scr.nowrap
  have hroom := hO.room
  have hw28 := hO.w28
  have h8 := hdr_lt_slot a.w 8 (show 31 < 32 by decide)
  have hi8 : 8 * 32 ≤ inner a.w := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner a.w + slot a.w 8 ≤ a.Z := by unfold tabBytes32 at hroom; omega_arith
  have eWs : sWs = 29 := rfl
  refine WP.mono (wsSetup_ok (len := a.len) hO hsl hslW hL h1 hlw) fun t ⟨hc, _, f, k⟩ => ?_
  have hb : ∀ i < 32, i ≠ sWs → word t.mem a.B (8 * i) = word s.mem a.B (8 * i) := fun i hi hne =>
    f.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  exact ⟨_, bs, hc, by rw [hb _ hsl hslW]; exact hL, by rw [hb _ hsp hspW]; exact hP,
    hsrc.congrK (InScr.of_frm f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) k, hl, h1, hlw, hodd, hO.w2, hw28⟩

theorem m2_lpre {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (a : MPub) (s : State) (h : M2 sp sl a s) :
    LPre aN sp sl a.bp s := by
  obtain ⟨mi, bs, hc, hL, hP, hsrc, hl, h1, hlw, -, hw2', hw28⟩ := h
  have hw2 : 2 ≤ a.wx := by unfold MPub.wx wsWords; omega_arith
  have hwx : a.wx ≤ a.w := by unfold MPub.wx wsWords; omega_arith
  exact ⟨mi, bs, hc, hw2, hwx, show a.w < 2 ^ 30 by omega_arith, by decide, hsp, hsl, hP, by rw [hl]; exact hL, hl,
    hsrc, by omega_arith, by omega_arith, show (bs.length + 7) / 8 ≤ a.wx by unfold MPub.wx wsWords; omega_arith⟩

theorem m2_m3 {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (a : MPub) (s : State) (h : M2 sp sl a s) :
    WP isa (seqs (loadArr aN sp sl)) s (M3 a) := by
  obtain ⟨mi, bs, hc, hL, hP, hsrc, hl, h1, hlw, hodd, hw2', hw28⟩ := h
  have hw2 : 2 ≤ a.wx := by unfold MPub.wx wsWords; omega_arith
  have hwx : a.wx ≤ a.w := by unfold MPub.wx wsWords; omega_arith
  refine WP.mono (primeLoad_ok hc hw2 hwx (by omega_arith) (show aN < 8 by decide) hsp hsl hP (by rw [hl]; exact hL)
    hsrc (by omega_arith) (by omega_arith) (show (bs.length + 7) / 8 ≤ a.wx by unfold MPub.wx wsWords; omega_arith))
    fun t ⟨hc₁, hX₁, _, _⟩ => ⟨mi, hc₁, ?_⟩
  rw [← wv_mod64 _ _ _ (show 1 ≤ a.wx by omega_arith), hX₁, Nat.mod_mod_of_dvd _ (by decide)]; exact hodd

theorem ldArr_ok {t : State} {G : Addr} {Zx wx : Nat} {mi : BitVec 64} (hg : Good t G Zx wx mi)
    (hZ : slot wx 8 ≤ Zx) {j : Nat} (hj : j < 8) :
    WP isa (.block [ldh .x8 (sArr j)]) t fun t' => t'.gpr .x0 = G ∧ t'.gpr .x8 = off G (slot wx j) :=
  WP.mono (WP.keep [.x8] (Q := fun t' => t'.gpr .x8 = off G (slot wx j))
    (by brun [hg.x0, hdr_enc (sArr_lt hj), hg.ld hZ (sArr_lt hj), hg.hdr.harr j hj]) rfl rfl rfl)
    fun t' ⟨h8, k⟩ => ⟨(k.gpr .x0 (by decide)).trans hg.x0, h8⟩

theorem m3_pin (a : MPub) (s : State) (h : M3 a s) :
    WP isa (.block [ldh .x8 (sArr aN)]) s fun t => t.gpr .x0 = off a.B (inner a.w) ∧
      t.gpr .x8 = off (off a.B (inner a.w)) (slot a.wx aN) := by
  obtain ⟨mi, hc, -⟩ := h
  exact ldArr_ok hc.good (Nat.le_refl _) (by decide)

/-- The block of `-m⁻¹` and `setWord`'s operands. -/
abbrev minvB : List Instr :=
  [ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]

theorem m3_m4 (a : MPub) (s : State) (h : M3 a s) :
    WP isa (.block minvB) s fun t => SWPre (a.ws, 0) t := by
  obtain ⟨mi, hc, hodd⟩ := h
  refine WP.mono (minvBlock_ok hc.good (Nat.le_refl _) hodd) fun t ⟨_, hm, h12, _, h13, k⟩ => ?_
  have o := writeW_outside s.mem (off a.B (inner a.w)) (d := 8 * sMinv) (t.gpr .x15) (by decide)
  rw [← hm] at o
  have f : Frm (off a.B (inner a.w)) [(8 * sMinv, 8)] s.mem t.mem := Frm.of_outside o (by simp)
  have hc' := hc.of_minv f (fun r hr => Or.inl (List.mem_singleton.mp hr)) k.wr (k.gpr .x0 (by decide))
  exact ⟨⟨_, hc'.good, Nat.le_refl _⟩, h12, h13⟩

theorem wsMod_eq (sp sl : Nat) : seqs (([.block (wsSetup sl ++ [enter])] : List (Prog isa)) ++ modSetup sp sl) =
    .seq (.block (([mov .x5 .x0] ++ wsEnd) ++ (wsNew sWs sl ++ [enter])))
      (seqs (loadArr aN sp sl ++ ([.block ([ldh .x8 (sArr aN)] ++ ([ld .x3 .x8] ++ minv ++
        [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])), setWord aOne] : List (Prog isa)))) := rfl

/-- A modulus' workspace: entered, the modulus, `-m⁻¹` and the number 1, given
that the taint analysis checks the blocks that read the slots `sp` and `sl`. -/
theorem wsMod_ct {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (hspW : sp ≠ sWs) (hslW : sl ≠ sWs)
    {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0, .x4]) (.block (wsNew sWs sl ++ [enter])) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x8 (sArr aN), ldh .x12 sW, movi .x7 0])
      hc₂).isSome = true)
    (hT₃ : (taint.check (Taint.ofRegs [.x0, .x5]) (.block [ldw .x1 .x5 sp, ldw .x2 .x5 sl, ldh .x8 (sArr aN)])
      hc₃).isSome = true) :
    RelCT isa (Two (M1 sp sl)) (seqs (([.block (wsSetup sl ++ [enter])] : List (Prog isa)) ++ modSetup sp sl)) fun _ _ => True := by
  rw [wsMod_eq]
  refine RelCT.seq (R := Two (M2 sp sl)) (RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (a : MPub) t =>
      (t.gpr .x0 = a.B ∧ t.gpr .x4 = off a.B (inner a.w)) ∧ WP isa (.block (wsNew sWs sl ++ [enter])) t
        (M2 sp sl a))
      [.x0] (pins_x0B MPub.B fun _ _ ⟨_, hO, _⟩ => hO.x0) (by taint_decide)
      fun a s h => wp_and (m1_pin sp sl a s h) (WP.block_append_iff.mp (m1_m2 hsp hsl hspW hslW a s h)))
    (two_piece [.x0, .x4] (pins_of (fun (a : MPub) r => if r = .x0 then a.B else off a.B (inner a.w))
      fun a s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1
        · exact h.1.2) hT₁ fun _ _ h => h.2))) ?_
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (R := Two M3)
    (two_post (two_map MPub.bp (m2_lpre hsp hsl) (loadArr_ct (by decide) hT₂ hT₃)) (m2_m3 hsp hsl)) ?_)
  refine RelCT.seq (R := Two fun (a : MPub) t => SWPre (a.ws, 0) t) (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := fun (a : MPub) t => (t.gpr .x0 = off a.B (inner a.w) ∧
        t.gpr .x8 = off (off a.B (inner a.w)) (slot a.wx aN)) ∧
      WP isa (.block ([ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])) t
        fun t => SWPre (a.ws, 0) t)
      [.x0] (pins_x0B (fun a => off a.B (inner a.w)) fun _ _ ⟨_, hc, _⟩ => hc.x0) (by taint_decide)
      fun a s h => wp_and (m3_pin a s h) (WP.block_append_iff.mp (m3_m4 a s h)))
    (two_piece [.x0, .x8] (pins_of (fun (a : MPub) r => if r = .x0 then off a.B (inner a.w) else
        off (off a.B (inner a.w)) (slot a.wx aN))
      fun a s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1
        · exact h.1.2) (by taint_decide) fun _ _ h => h.2))) ?_
  exact two_map (fun a : MPub => (a.ws, 0)) (fun _ _ h => h) (setWord_ct (by decide) (by taint_decide))

theorem sp0_sp1 (a : DPub) (s : State) (h : SetupP a s) : WP isa (.block head) s (SP1 a) := by
  obtain ⟨pb, hs, h0, hk1, hk2, hZ, hD, hK, hsrc, hl, hodd⟩ := h
  have ew : 8 * a.w ≤ a.k + 7 ∧ a.k ≤ 8 * a.w := by unfold DPub.w; omega_arith
  have hn := hs.nowrap
  have hroom := room_k hk1 hZ
  rw [show (a.k + 7) / 8 = a.w from rfl] at hroom
  have h8 := hdr_lt_slot a.w 8 (show 31 < 32 by decide)
  have eW6 : sW = 6 := rfl
  have eA8 : sArr 0 = 8 := rfl
  have hi8 : 8 * 32 ≤ inner a.w := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner a.w + slot a.w 8 ≤ a.Z := by unfold tabBytes32 at hroom; omega_arith
  refine WP.mono (head_ok hs h0 (show slot a.w 8 ≤ a.Z by unfold inner tabBytes32 at hroom; omega_arith) (by omega_arith) hK)
    fun s₁ ⟨_, hW, hA, f₁, k₁⟩ => ?_
  have hr₁ : ∀ i < 32, i ≠ sW → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word s₁.mem a.B (8 * i) = word s.mem a.B (8 * i) := fun i hi h1 h2 => f₁.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  exact ⟨pb, ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans h0, hW, hA, hroom, by omega_arith, by omega_arith⟩, hk1, hk2, hZ,
    by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hD,
    by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hK,
    hsrc.congrK (InScr.of_frm f₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) k₁, hl, hodd⟩

/-- p's workspace's public data. -/
abbrev DPub.m (a : DPub) : MPub := ⟨a.B, a.Z, a.w, a.k, a.dp⟩

theorem sp1_m1 (a : DPub) (s : State) (h : SP1 a s) : M1 sDom sK a.m s := by
  obtain ⟨pb, hO, hk1, hk2, hZ, hD, hK, hsrc, hl, hodd⟩ := h
  have ew : 8 * a.w ≤ a.k + 7 ∧ a.k ≤ 8 * a.w := by unfold DPub.w; omega_arith
  exact ⟨pb, hO, hK, hD, hsrc, hl, show 1 ≤ a.k by omega_arith, show a.k ≤ 8 * a.w by omega_arith, hodd⟩

/-- `head`, the workspaces, p, `-p⁻¹` and the number 1. -/
theorem setup_ct : RelCT isa (Two SetupP) (seqs (([.block head] : List (Prog isa)) ++ pSetup)) fun _ _ => True := by
  refine RelCT.seq (R := Two SP1) (two_piece [.x0] (pins_x0B DPub.B fun _ _ ⟨_, _, h0, _⟩ => h0) (by taint_decide)
    sp0_sp1) ?_
  exact two_map DPub.m sp1_m1 (wsMod_ct (by decide) (by decide) (by decide) (by decide) (by taint_decide)
    (by taint_decide) (by taint_decide))

end VG.Proof.Ffdh.AArch64
