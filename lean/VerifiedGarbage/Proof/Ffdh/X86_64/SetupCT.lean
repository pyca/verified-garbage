module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs

import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push

/-!
# FFDH on X86_64: the front in constant time

The check of p (`domHead_ct`) and the workspaces with p, `-p⁻¹` and the
number 1 (`setup_ct`) leak the same in runs with the same working space,
domain pointer and p's length (`DPub`), whatever p: between the pieces,
each run satisfies a stage (`SP1` … `SP3`, `SWPre`) by their correctness,
and the registers a piece's addresses and loop counts come from are fixed
by the stage.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (wsEnd wsNew loadArr leave ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

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
  Scr s a.B a.Z ∧ s.gpr .rdi = a.B ∧ 256 ≤ a.Z ∧ word s.mem a.B (8 * sDom) = a.dp ∧
    word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.k

/-! ## The workspaces -/

/-- `setup_ok`'s hypotheses. -/
def SetupP (a : DPub) (s : State) : Prop :=
  ∃ pb : List Byte, Scr s a.B a.Z ∧ s.gpr .rdi = a.B ∧ 64 ≤ a.k ∧ a.k ≤ 1024 ∧ 128 * a.k + 256 ≤ a.Z ∧
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

theorem m1_m2 {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (hspW : sp ≠ sWs) (hslW : sl ≠ sWs) (a : MPub)
    (s : State) (h : M1 sp sl a s) : WP isa (seqs (wsSetup sl ++ ([.block [enter]] : List (Prog isa)))) s (M2 sp sl a) := by
  obtain ⟨bs, hO, hL, hP, hsrc, hl, h1, hlw, hodd⟩ := h
  have hn := hO.scr.nowrap
  have hroom := hO.room
  have hw28 := hO.w28
  have h8 := hdr_lt_slot a.w 8 (show 31 < 32 by decide)
  have hi8 : 8 * 32 ≤ inner a.w := by simp only [inner, slot, hdrBytes]; omega
  have hiZ : inner a.w + slot a.w 8 ≤ a.Z := by unfold tabBytes at hroom; omega
  have eWs : sWs = 29 := rfl
  refine WP.mono (wsSetup_ok (len := a.len) hO hsl hslW hL h1 hlw) fun t ⟨hc, _, _, f, k⟩ => ?_
  have hb : ∀ i < 32, i ≠ sWs → word t.mem a.B (8 * i) = word s.mem a.B (8 * i) := fun i hi hne =>
    f.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  exact ⟨_, bs, hc, by rw [hb _ hsl hslW]; exact hL, by rw [hb _ hsp hspW]; exact hP,
    hsrc.congrK (InScr.of_frm f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) k, hl, h1, hlw, hodd, hO.w2, hw28⟩

theorem m2_lpre {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (a : MPub) (s : State) (h : M2 sp sl a s) :
    LPre aN sp sl a.bp s := by
  obtain ⟨mi, bs, hc, hL, hP, hsrc, hl, h1, hlw, -, hw2', hw28⟩ := h
  have hw2 : 2 ≤ a.wx := by unfold MPub.wx wsWords; omega
  have hwx : a.wx ≤ a.w := by unfold MPub.wx wsWords; omega
  exact ⟨mi, bs, hc, hw2, hwx, show a.w < 2 ^ 30 by omega, by decide, hsp, hsl, hP, by rw [hl]; exact hL, hl,
    hsrc, by omega, by omega, show (bs.length + 7) / 8 ≤ a.wx by unfold MPub.wx wsWords; omega⟩

theorem m2_m3 {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (a : MPub) (s : State) (h : M2 sp sl a s) :
    WP isa (seqs (loadArr aN sp sl)) s (M3 a) := by
  obtain ⟨mi, bs, hc, hL, hP, hsrc, hl, h1, hlw, hodd, hw2', hw28⟩ := h
  have hw2 : 2 ≤ a.wx := by unfold MPub.wx wsWords; omega
  have hwx : a.wx ≤ a.w := by unfold MPub.wx wsWords; omega
  refine WP.mono (primeLoad_ok hc hw2 hwx (by omega) (show aN < 8 by decide) hsp hsl hP (by rw [hl]; exact hL)
    hsrc (by omega) (by omega) (show (bs.length + 7) / 8 ≤ a.wx by unfold MPub.wx wsWords; omega))
    fun t ⟨hc₁, hX₁, _, _⟩ => ⟨mi, hc₁, ?_⟩
  rw [← wv_mod64 _ _ _ (show 1 ≤ a.wx by omega), hX₁, Nat.mod_mod_of_dvd _ (by decide)]; exact hodd

theorem sp0_sp1 (a : DPub) (s : State) (h : SetupP a s) : WP isa (.block VG.Impl.Rsa.X86_64.head) s (SP1 a) := by
  obtain ⟨pb, hs, h0, hk1, hk2, hZ, hD, hK, hsrc, hl, hodd⟩ := h
  have ew : 8 * a.w ≤ a.k + 7 ∧ a.k ≤ 8 * a.w := by unfold DPub.w; omega
  have hn := hs.nowrap
  have hroom := room_k hk1 hZ
  rw [show (a.k + 7) / 8 = a.w from rfl] at hroom
  have h8 := hdr_lt_slot a.w 8 (show 31 < 32 by decide)
  have eW6 : sW = 6 := rfl
  have eA8 : sArr 0 = 8 := rfl
  have hi8 : 8 * 32 ≤ inner a.w := by simp only [inner, slot, hdrBytes]; omega
  have hiZ : inner a.w + slot a.w 8 ≤ a.Z := by unfold tabBytes at hroom; omega
  refine WP.mono (head_ok hs h0 (show slot a.w 8 ≤ a.Z by unfold inner tabBytes at hroom; omega) (by omega) hK)
    fun s₁ ⟨_, hW, hA, f₁, k₁⟩ => ?_
  have hr₁ : ∀ i < 32, i ≠ sW → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word s₁.mem a.B (8 * i) = word s.mem a.B (8 * i) := fun i hi h1 h2 => f₁.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  exact ⟨pb, ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans h0, hW, hA, hroom, by omega, by omega⟩, hk1, hk2, hZ,
    by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hD,
    by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hK,
    hsrc.congrK (InScr.of_frm f₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) k₁, hl, hodd⟩

/-- p's workspace's public data. -/
abbrev DPub.m (a : DPub) : MPub := ⟨a.B, a.Z, a.w, a.k, a.dp⟩

theorem sp1_m1 (a : DPub) (s : State) (h : SP1 a s) : M1 sDom sK a.m s := by
  obtain ⟨pb, hO, hk1, hk2, hZ, hD, hK, hsrc, hl, hodd⟩ := h
  have ew : 8 * a.w ≤ a.k + 7 ∧ a.k ≤ 8 * a.w := by unfold DPub.w; omega
  exact ⟨pb, hO, hK, hD, hsrc, hl, show 1 ≤ a.k by omega, show a.k ≤ 8 * a.w by omega, hodd⟩


end VG.Proof.Ffdh.X86_64
