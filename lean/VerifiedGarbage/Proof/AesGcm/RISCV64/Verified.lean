module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-! ### `AesGcm.RISCV64.CTOpen`, which this module and modules that import it used -/

section

/-! ### `AesGcm.RISCV64.Open`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: the pieces of `vg_aes_gcm_open_bitsliced`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTCrypt.lean`): `open` checks the tag length; if it is
allowed, it computes the tag of the ciphertext into `W + 112` (`oneAad`,
`oneTag 112`), copies the received tag to `W + 256` and compares the first
`tag_len` bytes of each (`recv`, `cmp 112`), and decrypts the data in place
only if they are equal; `a0` is the result. Until the data is decrypted,
everything `open` writes is in the working space `W` or the stack below
`sp` (`Frame (wF W sp)`), which every buffer is apart from.

The same body, out of place (`openWithB true true`), is
`vg_aes_gcm_open_to_bitsliced`'s, which reads the ciphertext at `a6` and
writes the plaintext to a destination `Dst` apart from it: `OPre o` is what
the body needs of its arguments, wherever the entry found them, and `SO2`
the state after the entry, from which `OpenBs.lean` proves the body
(`openB_head`, `openB_tail`, `openB_body`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph fullTag zeros padLen j0 inc32 gctr decryptWith openResult)

/-- What `open` promises, given the result `a0` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .a0 = 1 ∧ bytesAt s.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = pt
  | none => s.gpr .a0 = 0 ∧ bytesAt s.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .a0 = 0)
    (hd : bytesAt s.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .a0 = 1)
    (hd : bytesAt s.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- What the end of `open` leaves for `restore`. -/
structure OpenOut (s₀ s : State) : Prop where
  s0 : s.gpr .s0 = stackArg s₀ 2
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem (stackArg s₀ 2) s₀
  post : OpenPost s₀ s

/-- An environment for a state's own registers, after a step that changes
only registers the pieces do not need pinned: `s0`–`s2` and the regions are
kept. -/
theorem Env.self' {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (he : Env V sp s)
    (h0 : s'.gpr .s0 = s.gpr .s0) (h1 : s'.gpr .s1 = s.gpr .s1) (h2 : s'.gpr .s2 = s.gpr .s2) (hk : Keeps s s') :
    Env s'.gpr sp s' :=
  ⟨fun _ _ => rfl, hk.sp.trans he.sp, by
    rw [h2, h1, h0, he.fr _ (by decide), he.fr _ (by decide), he.fr _ (by decide)]
    exact he.perm.of_eq hk.rd hk.wr, by
    rw [h2, h1, h0, he.fr _ (by decide), he.fr _ (by decide), he.fr _ (by decide), hk.sp]
    exact he.stk⟩

/-- An environment for a state's own registers, after a step that changes
only `s8` among those the environment pins. -/
theorem Env.self {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (he : Env V sp s)
    (hg : ∀ r, r ≠ .s8 → s'.gpr r = s.gpr r) (hk : Keeps s s') : Env s'.gpr sp s' :=
  he.self' (hg _ (by decide)) (hg _ (by decide)) (hg _ (by decide)) hk

/-- `W` and the stack below `sp`. -/
abbrev wF (W sp : Addr) : List Region := [⟨W, 2560⟩, below sp 2048]

section
variable {W sp : Addr}

/-- What `oneAad`, `oneTag 112`, `recv` and `cmp 112` write is in `W` or below `sp`. -/
theorem inW_j0 : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W sp, ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem inW_ot : ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp, ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem inW_at {d : Nat} (hd : d + 16 ≤ 2560) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., Lay.wSub hd⟩

theorem inW_one : ∀ r ∈ [oneR W], ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩

/-- The first counter block is apart from what `oneTag 112`, `recv` and `cmp 112` write. -/
theorem cb_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W) (hk : StkOk c (W + BitVec.ofNat 64 16) W sp) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.st_st (st := W + BitVec.ofNat 64 16) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide))
      (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact hk.st.sub_left (Lay.stSub (by decide))
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)

/-- A slot of the addresses (`W + d`, `232 ≤ d < 256`) is apart from what
`oneTag 112`, `recv` and `cmp 112` write. -/
theorem slot_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W) (hk : StkOk c (W + BitVec.ofNat 64 16) W sp)
    {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 256) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (a := 0) (n := 48) (by decide) (.inr ⟨by omega_using [hd], by omega_using [hd]⟩)).symm.sub_right
      (by simpa using Region.sub_prefix (base := W + BitVec.ofNat 64 16) (show 48 ≤ 48 by decide))
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact hk.w.sub_left (Lay.wSub (by omega_using [hd]))
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)

end

/-- A buffer apart from `W` and the stack below `sp` is as it was. -/
theorem bytes_W {m m' : Mem} {W sp p : Addr} {n : Nat} (hf : Frame (wF W sp) m m')
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hs : (⟨p, n⟩ : Region).Disjoint (below sp 2048)) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd
    · exact hs) hn

/-- Whether the computed tag, cut to the tag length `TL`, is the received
one at `T`. -/
abbrev OpenTagOk (s₀ : State) (T : Addr) (TL : Nat) : Prop :=
  (fullTag (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat) (ctxH s₀.mem (s₀.gpr .a0))
      (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat) (bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat)
      (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)).take TL = bytesAt s₀.mem T TL

/-- `OpenTagOk` for `vg_aes_gcm_open`'s tag, its first two stack arguments. -/
abbrev openTagOk (s₀ : State) : Prop := OpenTagOk s₀ (stackArg s₀ 0) (stackArg s₀ 1).toNat

/-- What `open`'s body needs of its arguments: the context, nonce, additional
data and data in `a0`–`a7`, the working space `W` and the tag `T` of `TL`
bytes, wherever the entry found them, and where the plaintext goes, `Dst`:
the data itself in place (`o` false), or a buffer apart from it. -/
structure OPre (o : Bool) (s₀ : State) (W T Dst : Addr) (TL : Nat) : Prop where
  ctx : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr)
  nonce : Covers [⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩] (s₀.rd ++ s₀.wr)
  aad : Covers [⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩] (s₀.rd ++ s₀.wr)
  src : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] (s₀.rd ++ s₀.wr)
  tag : Covers [⟨T, TL⟩] (s₀.rd ++ s₀.wr)
  w : Covers [⟨W, 2560⟩] s₀.wr
  dst : Covers [⟨Dst, (s₀.gpr .a7).toNat⟩] s₀.wr
  dcW : (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  dnW : (⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩ : Region).Disjoint ⟨W, 2560⟩
  daW : (⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩ : Region).Disjoint ⟨W, 2560⟩
  dsW : (⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩ : Region).Disjoint ⟨W, 2560⟩
  dtW : (⟨T, TL⟩ : Region).Disjoint ⟨W, 2560⟩
  dDW : (⟨Dst, (s₀.gpr .a7).toNat⟩ : Region).Disjoint ⟨W, 2560⟩
  dcD : (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint ⟨Dst, (s₀.gpr .a7).toNat⟩
  fc : (s₀.gpr .a0).toNat + 256 ≤ 2 ^ 64
  fn : (s₀.gpr .a2).toNat + (s₀.gpr .a3).toNat ≤ 2 ^ 64
  fa : (s₀.gpr .a4).toNat + (s₀.gpr .a5).toNat ≤ 2 ^ 64
  fs : (s₀.gpr .a6).toNat + (s₀.gpr .a7).toNat ≤ 2 ^ 64
  fD : Dst.toNat + (s₀.gpr .a7).toNat ≤ 2 ^ 64
  fW : W.toNat + 2560 ≤ 2 ^ 64
  tl : TL < 2 ^ 64
  bufs : ∀ r ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩,
    ⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩, ⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩, ⟨Dst, (s₀.gpr .a7).toNat⟩, ⟨T, TL⟩,
    ⟨W, 2560⟩], r.Disjoint (below s₀.sp 2048)
  al : s₀.sp.toNat % 16 = 0
  ge : 2048 ≤ s₀.sp.toNat
  rounds : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14
  ca : (s₀.gpr .a0).toNat % 8 = 0
  wa : W.toNat % 8 = 0
  alias : Alias o (s₀.gpr .a6) Dst (s₀.gpr .a7).toNat

section
variable {o : Bool} {s₀ : State} {W T Dst : Addr} {TL : Nat} (h : OPre o s₀ W T Dst TL)
include h

theorem OPre.lay : Lay (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W := oneLay h.fc h.fW h.dcW h.ca h.wa

theorem OPre.stk : StkOk (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀.sp :=
  ⟨h.bufs _ (by simp), (h.bufs _ (by simp)).sub_left (Lay.wSub (by decide)), h.bufs _ (by simp), h.al, h.ge⟩

theorem OPre.dsrc : DataOk (W + BitVec.ofNat 64 16) W s₀ (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
  ⟨h.src, (s₀.gpr .a7).isLt, h.fs, h.dsW.sub_right (Lay.wSub (by decide)), h.dsW, h.bufs _ (by simp)⟩

theorem OPre.ddst : DataW (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀ Dst (s₀.gpr .a7).toNat :=
  ⟨⟨covers_left h.dst, (s₀.gpr .a7).isLt, h.fD, h.dDW.sub_right (Lay.wSub (by decide)), h.dDW,
    h.bufs _ (by simp)⟩, h.dst, h.dcD⟩

end

/-- After the entry of `open`'s body, from `s₀`, with the working space `W`
and the tag's address `T`: `SO1`, but for the slots the entry writes, and,
out of place, the distance to the destination at `W + dstO`. -/
structure SO2 (o : Bool) (W T Dst : Addr) (s₀ s₁ : State) : Prop where
  keeps : Keeps' s₀ s₁
  saved : SavedAt s₁.mem W s₀
  frame : Frame (wF W s₀.sp) s₀.mem s₁.mem
  aad : s₁.mem.readW (W + BitVec.ofNat 64 aadO) 64 = s₀.gpr .a4
  dat : s₁.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6
  dst : o = true → s₁.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6
  s0 : s₁.gpr .s0 = W
  s1 : s₁.gpr .s1 = W + BitVec.ofNat 64 16
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s3 : s₁.gpr .s3 = s₀.gpr .a1
  s4 : s₁.gpr .s4 = s₀.gpr .a2
  s5 : s₁.gpr .s5 = s₀.gpr .a3
  s7 : s₁.gpr .s7 = s₀.gpr .a3
  s10 : s₁.gpr .s10 = s₀.gpr .a5
  s11 : s₁.gpr .s11 = s₀.gpr .a7
  s9 : s₁.gpr .s9 = T

/-- In place, `SO1`. -/
theorem SO1.so2 {W T Dst : Addr} {s₀ s₁ : State} (h : SO1 W T s₀ s₁) : SO2 false W T Dst s₀ s₁ :=
  ⟨h.keeps, h.saved, h.frame.sub inW_one, h.aad, h.dat, nofun, h.s0, h.s1, h.s2, h.s3, h.s4, h.s5, h.s7,
    h.s10, h.s11, h.s9⟩

/-- After a step that changes no register the entry set but `t0` and `s8`. -/
theorem SO2.keep {o : Bool} {W T Dst : Addr} {s₀ s₁ s₂ : State} (h1 : SO2 o W T Dst s₀ s₁)
    (hg : ∀ r, r ≠ .t0 → r ≠ .s8 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO2 o W T Dst s₀ s₂ :=
  ⟨⟨hk.rd.trans h1.keeps.rd, hk.wr.trans h1.keeps.wr, hk.sp.trans h1.keeps.sp⟩, hk.mem ▸ h1.saved,
    hk.mem ▸ h1.frame, hk.mem ▸ h1.aad, hk.mem ▸ h1.dat, fun ho => hk.mem ▸ h1.dst ho,
    by rw [hg _ (by decide) (by decide)]; exact h1.s0, by rw [hg _ (by decide) (by decide)]; exact h1.s1,
    by rw [hg _ (by decide) (by decide)]; exact h1.s2, by rw [hg _ (by decide) (by decide)]; exact h1.s3,
    by rw [hg _ (by decide) (by decide)]; exact h1.s4, by rw [hg _ (by decide) (by decide)]; exact h1.s5,
    by rw [hg _ (by decide) (by decide)]; exact h1.s7, by rw [hg _ (by decide) (by decide)]; exact h1.s10,
    by rw [hg _ (by decide) (by decide)]; exact h1.s11, by rw [hg _ (by decide) (by decide)]; exact h1.s9⟩

/-- After the entry, the environment. -/
theorem SO2.env {o : Bool} {W T Dst : Addr} {s₀ s₁ : State} (h1 : SO2 o W T Dst s₀ s₁)
    (hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr)) (hW : Covers [⟨W, 2560⟩] s₀.wr)
    (hk : StkOk (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀.sp) :
    Env s₁.gpr s₀.sp s₁ := by
  obtain perm : Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₁ :=
    (⟨hC, covers_off hW (show 16 + 80 ≤ 2560 by decide) (by decide), hW⟩ :
      Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀).of_eq h1.keeps.rd h1.keeps.wr
  exact ⟨fun _ _ => rfl, h1.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.keeps.sp]; exact hk⟩

/-- Out of place, the distance into `s9`; in place, nothing. -/
theorem deltaArg_ok {o : Bool} {s : State} {W δ : Addr} (h31 : s.gpr .s0 = W) (wa : W.toNat % 8 = 0)
    (hW : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 dstO) 8)
    (hδ : o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = δ) :
    WP isa (.block (deltaArg o)) s fun s' => (o = true → s'.gpr .s9 = δ) ∧
      (∀ r, r ≠ .s9 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  cases o
  · simp only [deltaArg, Bool.false_eq_true, ↓reduceIte]
    exact WP.block_nil ⟨nofun, fun _ _ => rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
  · simp only [deltaArg, ↓reduceIte]
    exact Steps.wp_ld (off := dstO) (a := W + BitVec.ofNat 64 dstO) (by decide) (by rw [h31])
      (Spill.al8 wa (by decide)) hW fun s₁ u₁ => WP.block_nil ⟨fun _ => by rw [u₁.gpr, hδ rfl],
        fun r hr => u₁.other r hr, ⟨u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩⟩

/-- What `open`'s body leaves before its end (`openFin`): the result in `a0`
and the plaintext at `Dst`; in place, the data as it was if the tag is
wrong. -/
structure BodyOut (o : Bool) (s₀ : State) (W T Dst : Addr) (TL : Nat) (s : State) : Prop where
  s0 : s.gpr .s0 = W
  s11 : s.gpr .s11 = s₀.gpr .a7
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem W s₀
  dat : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6
  dst : o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6
  a0 : s.gpr .a0 = BitVec.ofNat 64 (if OpenTagOk s₀ T TL then 1 else 0)
  good : OpenTagOk s₀ T TL → bytesAt s.mem Dst (s₀.gpr .a7).toNat =
    gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
      (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
      (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)
  bad : ¬OpenTagOk s₀ T TL → o = false → bytesAt s.mem Dst (s₀.gpr .a7).toNat =
    bytesAt s₀.mem Dst (s₀.gpr .a7).toNat

/-- What `open`'s body leaves for its end (`openFin`): the result in `a0`, 0
if the tag length `TL` is not allowed or the tag is wrong, and then (in
place) the data as it was; otherwise 1 and the plaintext at `Dst`. -/
structure BodyRes (o : Bool) (s₀ : State) (W T Dst : Addr) (TL : Nat) (s : State) : Prop where
  s0 : s.gpr .s0 = W
  s11 : s.gpr .s11 = s₀.gpr .a7
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem W s₀
  dat : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6
  dst : o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6
  good : Spec.Gcm.tagLenOk TL = true ∧ OpenTagOk s₀ T TL →
    s.gpr .a0 = 1 ∧ bytesAt s.mem Dst (s₀.gpr .a7).toNat =
      gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)
  bad : ¬(Spec.Gcm.tagLenOk TL = true ∧ OpenTagOk s₀ T TL) →
    s.gpr .a0 = 0 ∧ (o = false → bytesAt s.mem Dst (s₀.gpr .a7).toNat = bytesAt s₀.mem Dst (s₀.gpr .a7).toNat)

/-- The contract's postcondition, from `OpenPost`, through `restore`. -/
theorem openPost_out {s₀ s s' : State} (op : OpenPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .a0 = s.gpr .a0) :
    openRISCV64.post s₀ s' := by
  unfold OpenPost at op
  unfold openRISCV64
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op <;> exact ⟨by rw [op.1]; rfl, op.2⟩

/-- After a step that changes no register the entry set but `t0` and `s8`. -/
theorem SO1.keep {W T : Addr} {s₀ s₁ s₂ : State} (h1 : SO1 W T s₀ s₁)
    (hg : ∀ r, r ≠ .t0 → r ≠ .s8 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO1 W T s₀ s₂ :=
  ⟨⟨hk.rd.trans h1.keeps.rd, hk.wr.trans h1.keeps.wr, hk.sp.trans h1.keeps.sp⟩, hk.mem ▸ h1.saved,
    hk.mem ▸ h1.frame, hk.mem ▸ h1.aad, hk.mem ▸ h1.dat,
    by rw [hg _ (by decide) (by decide)]; exact h1.s0, by rw [hg _ (by decide) (by decide)]; exact h1.s1,
    by rw [hg _ (by decide) (by decide)]; exact h1.s2, by rw [hg _ (by decide) (by decide)]; exact h1.s3,
    by rw [hg _ (by decide) (by decide)]; exact h1.s4, by rw [hg _ (by decide) (by decide)]; exact h1.s5,
    by rw [hg _ (by decide) (by decide)]; exact h1.s7, by rw [hg _ (by decide) (by decide)]; exact h1.s10,
    by rw [hg _ (by decide) (by decide)]; exact h1.s11, by rw [hg _ (by decide) (by decide)]; exact h1.s9,
    by rw [hg _ (by decide) (by decide)]; exact h1.t1⟩

end VG.Proof.AesGcm.RISCV64

end

end

/-! ### `AesGcm.RISCV64.CTVerify`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_verify_bitsliced`'s check is constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTOpen.lean`): the invariant fixes what `finish`'s
does (`FinI`), and the received tag's address and length (`s9`, `s8`);
the branch on the tag length is on that public length, and the comparison
does not branch.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- In `verify`, after the entry: the received tag's `tl` bytes at `Tp`,
apart from `W`, which the state may read. -/
def VerI (c st w sp : Addr) (R : Nat) (A T Tp : BitVec 64) (tl : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s9 = Tp ∧ V .s8 = BitVec.ofNat 64 tl ∧ Env V sp s ∧ Covers [⟨Tp, tl⟩] (s.rd ++ s.wr) ∧
    (⟨Tp, tl⟩ : Region).Disjoint ⟨w, 2560⟩

/-- `VerI`, and with the round keys bitsliced (`bs`), the buffer at `kb` in `s7`. -/
def VerIB (bs : Bool) (kb c st w sp : Addr) (R : Nat) (A T Tp : BitVec 64) (tl : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s9 = Tp ∧ V .s8 = BitVec.ofNat 64 tl ∧ Env V sp s ∧ Covers [⟨Tp, tl⟩] (s.rd ++ s.wr) ∧
    (⟨Tp, tl⟩ : Region).Disjoint ⟨w, 2560⟩ ∧ BkB bs kb V sp R s.mem w w 16 s

theorem tagLenOk_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8]) tagLenOk h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem recv_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s0]) recv h).isSome =
    true := ⟨_, by taint_decide⟩

theorem cmp_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s0]) (cmp 0) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem li3_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs []) (.block [.li .a0 0]) h).isSome =
    true := ⟨_, by taint_decide⟩

section
variable {c st w sp : Addr} (L : Lay c st w) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {A T Tp : BitVec 64}
  {tl : Nat}
include L hR

/-- `verify` after the tag length is known to be allowed; with the round keys
bitsliced (`bs`), the buffer at `kb` in `s7`. -/
theorem verOkB_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {kb : Addr} (t1 : 1 ≤ tl) (t16 : tl ≤ 16) :
    CT (VerIB bs kb c st w sp R A T Tp tl) (.seq recv (.seq (finTagB bs 0) (cmp 0))) := by
  refine CT.seq (J := VerIB bs kb c st w sp R A T Tp tl) ?_
    (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd, hb⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · refine WP.mono (recv_ok he (by rw [d]; exact L.wal) j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
      (by decide)))) fun s' ⟨_, fr, hg, hk⟩ => ⟨V, a, b, d, e, f, g, i, j, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd,
        fun hbs => ⟨(hb hbs).1, (hb hbs).2.frame hR fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (hb hbs).2.w.sub_right (Lay.wSub (by decide)))
          (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (L.v a b d).cw'.sub_right (Lay.wSub (by decide)))
          hk.rd hk.wr⟩⟩
  refine CT.seq (J := VerI c st w sp R A T Tp tl)
    ((finTagB_ct L (o := 0) (.inl rfl) hR).mono fun s ⟨V, a, b, d, e, f, g, _, _, he, _, _, hb⟩ =>
      ⟨V, a, b, d, e, f, g, he, hb⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd, hb⟩ => WP.mono (WP.with_rdwr (finTagB_ok (L.v a b d) (o := 0)
      (.inl rfl) (a := List.replicate (A.toNat % 16) 0) (ct := List.replicate T.toNat 0) he e hR rfl
      (by simp [f]) (by simp [g]) fun hbs => (hb hbs).2)) fun s' ⟨fo, rd, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, j, fo.env, by rw [rd, wr]; exact hT, hTd⟩) ?_
  obtain ⟨_, hc⟩ := cmp_taint
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, _, j₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · rw [h₁.s0, h₂.s0, d₁, d₂]

/-- The same, for correctness: `W` is kept in `s0`. -/
theorem verOkB_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {kb : Addr} (t1 : 1 ≤ tl) (t16 : tl ≤ 16) {s : State}
    (h : VerIB bs kb c st w sp R A T Tp tl s) :
    WP isa (.seq recv (.seq (finTagB bs 0) (cmp 0))) s fun s' => s'.gpr .s0 = w ∧ s'.sp = sp := by
  obtain ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd, hb⟩ := h
  refine WP.seq (WP.mono (recv_ok he (by rw [d]; exact L.wal) j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
    (by decide)))) fun s₁ ⟨_, fr, hg, hk⟩ => ?_)
  have he₁ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  refine WP.seq (WP.mono (finTagB_ok (L.v a b d) (o := 0) (.inl rfl) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he₁ e hR rfl (by simp [f]) (by simp [g]) fun hbs =>
      (hb hbs).2.frame hR fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (hb hbs).2.w.sub_right (Lay.wSub (by decide)))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (L.v a b d).cw'.sub_right (Lay.wSub (by decide)))
        hk.rd hk.wr) fun s₂ fo => ?_)
  refine WP.mono (cmp_ok fo.env (by rw [d]; exact L.wal) (o := 0) (.inl rfl) j t1 t16) fun s' ⟨_, _, hg', hk'⟩ =>
    ⟨by rw [hg' _ (by decide) (by decide) (by decide) (by decide) (by decide), fo.env.s0, d],
      by rw [hk'.sp, fo.env.sp]⟩

end

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: the pieces of `vg_aes_gcm_open_bitsliced`'s constant time

Untrusted: everything here is checked by Lean. The entry as for `seal`
(`CTSeal.lean`), then `tag_len` (`s8`), public, and the two branches of
`tagLenOk`. Once the tag length is allowed, the data is decrypted only if
the tags are equal, which may differ between two runs only as the result
does (the contract's `pub`: whether it succeeds). The invariants of the
pieces up to that comparison carry what the rest of each run reaches
(`CT.seqG`, from `openB_head`): the result in `s8`, which is then the same
in both runs (`openGoodB_ct`, `OpenBs.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- Two runs of `c₁` carry what a further `R` reaches from them. -/
theorem CT.seqG {I J Z : State → Prop} {c₁ R c₂ : Prog isa} (h₁ : CT I c₁) (w : ∀ s, I s → WP isa c₁ s J)
    (h₂ : CT (fun s => J s ∧ WP isa R s Z) c₂) : CT (fun s => I s ∧ WP isa (.seq c₁ R) s Z) (.seq c₁ c₂) :=
  CT.seq (h₁.mono fun _ h => h.1) (fun s h => WP.mono (WP.forall_det (w s h.1) (P := fun _ : Unit => True)
    (Q := fun _ s' => WP isa R s' Z) fun _ _ => WP.seq_iff.mp h.2) fun _ h => ⟨h.1, h.2 () trivial⟩) h₂

theorem openRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (stackArg t 1).toNat = true) :
    (openRes t).isSome = decide (openTagOk t) := by
  have e : openRes t = if openTagOk t then
      some (Spec.Gcm.gctr (Spec.Gcm.ctxCiph t.mem (t.gpr .a0) (t.gpr .a1).toNat)
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (t.gpr .a0)) (bytesAt t.mem (t.gpr .a2) (t.gpr .a3).toNat)))
        (bytesAt t.mem (t.gpr .a6) (t.gpr .a7).toNat)) else none := by
    simp only [openRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : openTagOk t
  · simp only [eq_true h, ite_true, decide_true, Option.isSome_some]
  · simp only [eq_false h, ite_false, decide_false, Option.isSome_none]

theorem openRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1])
    (.block (oneRest ++ ([.load .d .s8 .t1 8] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagLenOk_taint' : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8]) tagLenOk h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp112_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s0]) (cmp 112) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem nil_taint (b : List Instr) (h : b = [.li .a0 0] ∨ b = [mov .s5 .s7] ∨ b = [mov .s8 .a0] ∨
    b = [mov .a0 .s8]) : ∃ hh, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs []) (.block b) hh).isSome = true := by
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- Out of place, where `vg_aes_gcm_open_to` writes the data (`OD`) and the
distance to it at `W + dstO`. -/
def OX (o : Bool) (c W : Addr) (D Dst Ln : BitVec 64) (s : State) : Prop :=
  OD o c W D Dst Ln s ∧ (o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - D)

/-- `OneI`, with the tag's address `T` and length `TL` in `s9` and `s8`, and
where the data goes (`OX`). -/
def OneO (o : Bool) (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln T TL Dst : BitVec 64) (s : State) :
    Prop :=
  OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s9 = T ∧ s.gpr .s8 = TL ∧ Covers [⟨T, TL.toNat⟩] (s.rd ++ s.wr) ∧
    OX o c W D Dst Ln s

section
variable {o : Bool} {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln T TL Dst : BitVec 64}

theorem OX.frame {s s' : State} (h : OX o c W D Dst Ln s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 dstO, 8⟩ : Region).Disjoint r) : OX o c W D Dst Ln s' :=
  ⟨h.1.of_eq hrd hwr hsp, fun ho => (slot_keep hf hs).trans (h.2 ho)⟩

theorem OneO.frame {s s' : State} (h : OneO o c W sp R Np n Ad A D Ln T TL Dst s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 256 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneO o c W sp R Np n Ad A D Ln T TL Dst s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf (fun hd => hs ⟨hd.1, by omega_using [hd]⟩), (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.2.1), by rw [hrd, hwr]; exact h.2.2.2.1,
    h.2.2.2.2.frame hrd hwr hsp hf (hs (d := dstO) (by decide))⟩

/-- The result of the comparison in `s8`, for `b`. -/
abbrev Res (b : Bool) (s : State) : Prop := s.gpr .s8 = BitVec.ofNat 64 (if b then 1 else 0)

/-- The slots of the addresses are apart from what `oneTag 112` writes. -/
theorem slot_ot112 (L : Lay c (W + BitVec.ofNat 64 16) W) (hk : StkOk c (W + BitVec.ofNat 64 16) W sp) {d : Nat}
    (hd : 232 ≤ d ∧ d + 8 ≤ 256) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (a := 0) (n := 48) (by decide) (.inr ⟨by omega_using [hd], by omega_using [hd]⟩)).symm.sub_right
      (by simpa using Region.sub_prefix (base := W + BitVec.ofNat 64 16) (show 48 ≤ 48 by decide))
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact hk.w.sub_left (Lay.wSub (by omega_using [hd]))

/-- The slots are apart from a block of `W` at `e ≥ 256`. -/
theorem slot_at {e : Nat} (he : 256 ≤ e) (he' : e + 16 ≤ 2560) {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 256) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 e, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact Lay.w_w (.inl (by omega_using [he, hd])) (by omega_using [hd]) he'

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTd : (⟨T, TL.toNat⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) (t1 : 1 ≤ TL.toNat) (t16 : TL.toNat ≤ 16)
  (b : Bool)
include L hR hTd t1 t16

omit L hR hTd t1 t16 in
theorem deltaArg_taint (o : Bool) : ∃ hh, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s0])
    (.block ([mov .s8 .a0] ++ deltaArg o)) hh).isSome = true := by
  cases o <;> exact ⟨_, by taint_decide⟩

end

/-- `mv s5, s7` after `tagLenOk`: the entry's registers again. -/
theorem mov25_so1 {W T : Addr} {t₀ s₂ s₃ s₄ : State} (h2 : SO1 W T t₀ s₂)
    (g : ∀ r, r ≠ .t0 → r ≠ .s5 → s₃.gpr r = s₂.gpr r) (k : Keeps s₂ s₃) (u : Steps.Upd s₃ s₄ .s5 (s₃.gpr .s7)) :
    SO1 W T t₀ s₄ ∧ s₄.gpr .s8 = s₂.gpr .s8 := by
  refine ⟨h2.keep (fun r h0 _ => ?_) ⟨by rw [u.mem, k.mem], by rw [u.rd, k.rd], by rw [u.wr, k.wr],
    by rw [u.sp, k.sp]⟩, by rw [u.other _ (by decide), g _ (by decide) (by decide)]⟩
  by_cases e : r = .s5
  · subst e
    rw [u.gpr, g _ (by decide) (by decide), h2.s7, h2.s5]
  · rw [u.other r e, g r h0 e]

end VG.Proof.AesGcm.RISCV64

end

end

/-! ### `AesGcm.RISCV64.StreamCT`, which only this module used -/

section

/-! ### `AesGcm.RISCV64.StreamAad`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `absorb`'s arguments (`aadEntry_ok`); `absorb 16`
absorbs the data into the accumulator (`aad_run`), which keeps the rest of
the state (`streamAad_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)
open VG.Proof.Gcm (Absorbed Ctr)

/-- The entry: `absorb`'s arguments. -/
theorem aadEntry_ok {s : State} (hW : Covers [⟨s.gpr .a5, 2560⟩] s.wr) (hal : (s.gpr .a5).toNat % 8 = 0) :
    WP isa (.block streamAadPre) s fun s' => Entered s (s.gpr .a5) s' ∧
      s'.gpr .s0 = s.gpr .a5 ∧ s'.gpr .s1 = s.gpr .a1 ∧ s'.gpr .s2 = s.gpr .a0 ∧
      s'.gpr .s4 = s.gpr .a3 ∧ s'.gpr .s5 = s.gpr .a4 ∧
      s'.gpr .s6 = BitVec.ofNat 64 ((s.gpr .a2).toNat % 16) := by
  refine WP.block_append (WP.mono (save_ok (b := .a5) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .a0 = s.gpr .a0 := hg _ (by decide)
  have e4 : s₁.gpr .a1 = s.gpr .a1 := hg _ (by decide)
  have e5 : s₁.gpr .a2 = s.gpr .a2 := hg _ (by decide)
  have e6 : s₁.gpr .a3 = s.gpr .a3 := hg _ (by decide)
  have e7 : s₁.gpr .a4 = s.gpr .a4 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, e7, h31, and15]
  exact ⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩

/-- The regions `stream_aad` writes. -/
abbrev aadFrame (St W sp : Addr) : List Region := savedR W :: absFrame St W 16 sp

/-- After the entry: `absorb`'s precondition, for additional data `x` so far
of `aad_len` bytes modulo 16. -/
theorem aad_entry {s : State} (hs : streamAadRISCV64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .a2).toNat % 16) :
    WP isa (.block streamAadPre) s fun s₁ => Entered s (s.gpr .a5) s₁ ∧ s₁.gpr .s2 = s.gpr .a0 ∧
      s₁.gpr .s1 = s.gpr .a1 ∧ s₁.gpr .s0 = s.gpr .a5 ∧
      AbsIn s₁.gpr s.sp 16 (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x (s.gpr .a3) (s.gpr .a4).toNat s₁ ∧
      bytesAt s₁.mem (s.gpr .a3) (s.gpr .a4).toNat = bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat := by
  simp only [streamAadRISCV64] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww, hstk, -, -, hal⟩ := hs
  generalize hCtx : s.gpr .a0 = Ctx at *
  generalize hSt : s.gpr .a1 = St at *
  generalize hD : s.gpr .a3 = D at *
  generalize hn : (s.gpr .a4).toNat = n at *
  generalize hW : s.gpr .a5 = W at *
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .a4).isLt
  have hn' : s.gpr .a4 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hWc : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_mem (by simp)
  refine WP.mono (aadEntry_ok (by rw [hW]; exact hWc) (by rw [hW]; exact hal)) fun s₁ ⟨en, h31, h30, h29, h24, h25, h26⟩ => ?_
  rw [hW] at en h31
  rw [hSt] at h30
  rw [hCtx] at h29
  rw [hD] at h24
  rw [hn'] at h25
  have perm : Perm Ctx St W s₁ :=
    (⟨covers_mem (by rw [hrd, hwr]; simp), covers_mem (by rw [hwr]; simp), hWc⟩ : Perm Ctx St W s).of_eq
      en.keeps.rd en.keeps.wr
  have hk : StkOk Ctx St W s.sp := hstk.stk (by simp) (by simp) (by simp)
  have he : Env s₁.gpr s.sp s₁ :=
    ⟨fun _ _ => rfl, en.keeps.sp, by rw [h29, h30, h31]; exact perm, by rw [h29, h30, h31, en.keeps.sp]; exact hk⟩
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Offset.sub_base _ (by decide)
  have hdat : bytesAt s₁.mem D n = bytesAt s.mem D n :=
    bytesAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega_using [hn])
  have hH : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx := by
    rw [h29, ctxH_eq]
    exact blockAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dcw.sub_left (Offset.sub_base _ (by decide))).sub_right sW)
  refine ⟨en, h29, h30, h31, ⟨he, h24, h25, by rw [h26, hx], ?_, hH⟩, hdat⟩
  rw [h30, h31]
  exact ⟨by rw [en.keeps.rd, en.keeps.wr, hrd]; exact covers_mem (by simp), hlt, wd, dds, ddw,
    by rw [en.keeps.sp]; exact hstk.buf (by simp)⟩

/-- One run of `stream_aad`, for additional data `x` so far of `aad_len` bytes
modulo 16. -/
theorem aad_run [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (hs : streamAadRISCV64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .a2).toNat % 16) :
    WP isa streamAad s fun s' => abiPreserved s s' ∧
      (Absorbed s.mem (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x →
        Absorbed s'.mem (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .a0)) (x ++ bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)) ∧
      Frame (aadFrame (s.gpr .a1) (s.gpr .a5) s.sp) s.mem s'.mem := by
  have hs' := hs
  obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, hstk, a0, a1, a5⟩ := hs'
  have L₀ : Lay (s.gpr .a0) (s.gpr .a1) (s.gpr .a5) := Lay.of wc ws ww dcs dcw dsw a0 a1 a5
  refine WP.seq (WP.mono (aad_entry hs hx) fun s₁ ⟨en, h29, h30, h31, hIn, hdat⟩ => ?_)
  have dS : ∀ (d k : Nat), d + k ≤ 80 →
      (⟨s.gpr .a1 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (savedR (s.gpr .a5)) :=
    fun d k h => L₀.st_w h (.inr ⟨by decide, by decide⟩)
  have hA : ∀ (m : Mem), Frame [savedR (s.gpr .a5)] s.mem m →
      Absorbed s.mem (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
        (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x →
      Absorbed m (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
        (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x :=
    fun m hf ha => ha.congr (blockAt_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dS 16 16 (by decide))
      (bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dS 32 16 (by decide)).sub_left (Region.sub_prefix (Nat.le_of_lt (Nat.mod_lt _ (by decide)))))
        (by omega_using []))
  refine WP.seq (WP.mono (absorb_ok (L₀.v h29 h30 h31) (.inr rfl) hIn) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  rw [h30, h31] at f₂
  have hk := h₂.env.stk'
  rw [h29, h30, h31] at hk
  have hsv : SavedAt s₂.mem (s.gpr .a5) s := en.saved.frame f₂ (saved_absFrame L₀ (.inr rfl) hk)
  have e31 : s₂.gpr .s0 = s.gpr .a5 := (h₂.env.fr _ (by decide)).trans h31
  refine WP.mono (restore_ok e31 a5 (by
      have := h₂.env.perm.w; rw [h31] at this; exact Covers.right this) hsv h₂.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, fun ha => ?_, ?_⟩
  · have := h₂.abs
    rw [h30, hdat] at this
    rw [hm]; exact this (hA _ en.frame ha)
  · rw [hm]
    exact (en.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (f₂.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)

theorem streamAad_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (hs : streamAadRISCV64.pre s) :
    WP isa streamAad s fun s' => abiPreserved s s' ∧ streamAadRISCV64.post s s' := by
  have hz : (Spec.Gcm.zeros ((s.gpr .a2).toNat % 16)).length % 16 = (s.gpr .a2).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  refine WP.mono (WP.forall_det (P := fun (i : (Block → Block) × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .a1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .a0)) i.2.1 i.2.2 [] ∧
        s.gpr .a2 = BitVec.ofNat 64 i.2.2.length)
    (Q := fun i s' => StreamRepr s'.mem (s.gpr .a1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .a0)) i.2.1
      (i.2.2 ++ bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) [])
    (aad_run hs hz) fun ⟨ciph, iv, a⟩ ⟨hr, hl⟩ => ?_) fun s' ⟨⟨ga, _, _⟩, h⟩ =>
      ⟨ga, fun ciph iv a hr hl => h ⟨ciph, iv, a⟩ ⟨hr, hl⟩⟩
  have hx : a.length % 16 = (s.gpr .a2).toNat % 16 := by rw [hl, toNat_mod16]
  obtain ⟨hj, ha, hc⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have hs' := hs
  simp only [streamAadRISCV64] at hs'
  obtain ⟨-, -, -, -, -, -, dsw, -, -, ws, ww, hstk, -, -, -⟩ := hs'
  have dSt : ∀ r ∈ aadFrame (s.gpr .a1) (s.gpr .a5) s.sp, ∀ d, d + 16 ≤ 80 → (d + 16 ≤ 16 ∨ 48 ≤ d) →
      (⟨s.gpr .a1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro r hr d hd hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have st_off : ∀ e k, e + k ≤ 80 → (d + 16 ≤ e ∨ e + k ≤ d) →
        (⟨s.gpr .a1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨s.gpr .a1 + BitVec.ofNat 64 e, k⟩ :=
      fun e k he h => Offset.disjoint _ h (by omega_using [hd]) (by omega_using [he])
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Offset.sub_base _ (by decide))
    · exact st_off 16 16 (by decide) (by omega_using [hd'])
    · exact st_off 32 16 (by decide) (by omega_using [hd'])
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Offset.sub_base _ (by decide))
    · exact (hstk.buf (r := ⟨s.gpr .a1, 80⟩) (by simp)).sub_left (Offset.sub_base _ (by omega_using [hd]))
  refine WP.mono (aad_run hs hx) fun s' ⟨_, habs, hf⟩ => ?_
  refine Proof.Gcm.streamRepr_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [← hj]
    have := blockAt_frame hf fun r hr => by simpa using dSt r hr 0 (by decide) (.inl (by decide))
    simpa using this
  · exact habs ha
  · refine hc.congr ?_ ?_
    · exact blockAt_frame hf fun r hr => dSt r hr 48 (by decide) (.inr (by decide))
    · exact blockAt_frame hf fun r hr => dSt r hr 64 (by decide) (.inr (by decide))

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments; then `j0` (`j0_ct`) or `absorb 16`
(`absorb_ct`) from the invariants the entry's correctness gives; then the
exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem streamInitPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (.block streamInitPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem streamAadPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (.block streamAadPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem streamInit_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamInitRISCV64.pre streamInitRISCV64.pub streamInit := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a3) (σ₁.gpr .a4) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, -, a0, a3, a4⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw a0 a3 a4
  let I₀ : State → Prop := fun s => streamInitRISCV64.pre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧
    s.gpr .a1 = σ₁.gpr .a1 ∧ s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧
    s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    qsp.symm⟩, ?_⟩
  refine CT.seq (J := J0I (σ₁.gpr .a0) (σ₁.gpr .a3) (σ₁.gpr .a4) σ₁.sp (σ₁.gpr .a1) (σ₁.gpr .a2).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, esp⟩ => WP.mono (si_entry hs) fun s₁ ⟨_, h29, h30, h31, hJ, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamInitPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7]⟩) hc
  · rw [e3] at h29
    rw [e6] at h30
    rw [e7] at h31
    rw [e3, e4, e5, esp] at hJ
    exact ⟨s₁.gpr, _, h29, h30, h31, hJ⟩
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a4 ∧ s.sp = σ₁.sp) (j0_ct L)
    (fun s ⟨V, H, h29, h30, h31, hJ⟩ => WP.mono (j0_ok (L.v h29 h30 h31) hJ) fun s₂ h₂ =>
      ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a4) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamAad_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamAadRISCV64.pre streamAadRISCV64.pub streamAad := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a5) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, -, a0, a1, a5⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw a0 a1 a5
  let q := (σ₁.gpr .a2).toNat % 16
  have hq16 : q < 16 := Nat.mod_lt _ (by decide)
  let I₀ : State → Prop := fun s => streamAadRISCV64.pre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧
    s.gpr .a1 = σ₁.gpr .a1 ∧ s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧
    s.gpr .a5 = σ₁.gpr .a5 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := AbsI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a5) σ₁.sp 16 (σ₁.gpr .a3) (σ₁.gpr .a4).toNat q)
    ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamAadPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8]⟩) hc
  · have hx : (List.replicate q (0 : Byte)).length % 16 = (s.gpr .a2).toNat % 16 := by
      rw [List.length_replicate, e5, Nat.mod_mod]
    refine WP.mono (aad_entry hs hx) fun s₁ ⟨_, h29, h30, h31, hIn, _⟩ => ?_
    rw [e3] at h29 hIn
    rw [e4] at h30
    rw [e8] at h31
    rw [e6, e7, esp] at hIn
    exact ⟨s₁.gpr, _, _, h29, h30, h31, by rw [List.length_replicate, Nat.mod_mod], hIn⟩
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a5 ∧ s.sp = σ₁.sp) (absorb_ct L (.inr rfl) hq16)
    (fun s ⟨V, H, x, h29, h30, h31, _, hs⟩ => WP.mono (absorb_ok (L.v h29 h30 h31) (.inr rfl) hs)
      fun s₂ h₂ => ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a5) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64

end

end

/-! ### `AesGcm.RISCV64.CTCryptFn`, which only this module used -/

section

/-!
# AES-GCM on RISC-V: the text's arguments and absorption, for the streaming functions' constant time

Untrusted: everything here is checked by Lean. What the constant-time proofs
of `vg_aes_gcm_stream_encrypt_bitsliced` and `…_decrypt_bitsliced`
(`StreamBs.lean`) need of the arguments of the text (`textArgs_taint`) and
of `textAbsorb` (`ta_textAbsorb`), besides `crypt` (`cryptB_ct`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem textArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s11])
    (.block textArgs) h).isSome = true := ⟨_, by taint_decide⟩

section
variable {c st w sp D : Addr} {R : Nat} {N A T : BitVec 64}

theorem ta_exit {s : State} (h : TA c st w sp D N A T s) : s.gpr .s0 = w ∧ s.sp = sp :=
  let ⟨_, _, _, h31, _, _, _, _, he, _⟩ := h
  ⟨(he.fr _ (by decide)).trans h31, he.sp⟩

variable (L : Lay c st w)
include L

theorem ta_textAbsorb [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (h : TA c st w sp D N A T s) :
    WP isa textAbsorb s fun s' => s'.gpr .s0 = w ∧ s'.sp = sp := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩ := h
  exact WP.mono (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd) (by simp [h22])
    (by simp [h23])) fun s' ta => ⟨(ta.env.fr _ (by decide)).trans h31, ta.env.sp⟩

end

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_init`, `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad`, a
state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`), with the 2048 bytes of stack `vg_ghash`'s
frame takes (but for `init`, which does not call it).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' :=
  init_wp hs

theorem streamInit_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamInitRISCV64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ streamInitRISCV64.post s s' :=
  streamInit_wp hs

theorem streamAad_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamAadRISCV64.pre s) :
    ∃ t s', Exec isa streamAad s t s' ∧ abiPreserved s s' ∧ streamAadRISCV64.post s s' :=
  streamAad_wp hs

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamInitSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamAadSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a3 => 0x2000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified RISCV64.target init (Proof.AesGcm.initScratchContract RISCV64.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre,
      Spec.Gcm.initPost, initRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [initSat] using initSat)

theorem streamInit_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamInit (Proof.AesGcm.streamInitScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamInit_correct streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig,
      Spec.Gcm.streamInitPost, streamInitRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true]
      [streamInitSat] using streamInitSat)

theorem streamAad_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamAad (Proof.AesGcm.streamAadScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamAad_correct streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig,
      Spec.Gcm.streamAadPost, streamAadRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true]
      [streamAadSat] using streamAadSat)

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

end VG.Proof.AesGcm.RISCV64

/-! ## With the working space on the stack

Each function runs its code, proved with the working space as an argument,
in a frame of 2560 bytes that allocates it, the working space in the next
register (`Verified.stackScratchL`). `StreamBs.lean` registers them, without
secret residue.
-/

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract RISCV64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 init)
      (Spec.Gcm.initContract RISCV64.abi 2560) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre RISCV64.abi.ptrBits) (post := Spec.Gcm.initPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) init_verified (by decide) (by decide) (Proof.AesGcm.initPostOut_local _)
    initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { streamInitSat with wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    RISCV64.abi, RISCV64.argRegs] [streamInitFrameSat, streamInitSat] using streamInitFrameSat

theorem streamInit_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a4 streamInit)
      (Spec.Gcm.streamInitContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamInit_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamInitPostOut_local _ vs m m₁ m₂ r hl)
    streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { streamAadSat with wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    RISCV64.abi, RISCV64.argRegs] [streamAadFrameSat, streamAadSat] using streamAadFrameSat

theorem streamAad_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 streamAad)
      (Spec.Gcm.streamAadContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamAad_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamAadPostOut_local _ vs m m₁ m₂ r hl)
    streamAadFrameSat_pre

end VG.Proof.AesGcm.RISCV64
