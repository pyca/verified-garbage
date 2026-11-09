module

public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenToSplit
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.Fn
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# AES-GCM decryption out of place, in one pass, x86-64: the function

Untrusted: everything here is checked by Lean. The contract the proof of
`openToSplit` is written against, for a key context of kind `M` (`toSK M`):
`open_to`'s (`OpenTo.toK`), with a working space of 2560 bytes as a seventh
stack argument, and its proof (`openToSplit_wp`). It calls an instance of
`vg_aes_gcm_open_split` for its key context (`OpenSplitFn`), an internal
function whose contract is `Proof.AesGcm.openSplitX86_64M`. With `B` the
base of the 152 bytes of stack below the stack pointer (`rsp = B + 152`),
the function pushes `open_to`'s frame of eleven words at `P = B + 64`,
stores the call's seven stack arguments in its lowest seven words
(`ready_wp`), calls `vg_aes_gcm_open_split` (`called_wp`), which reads the
ciphertext at `src` and writes only `dst`, `work` and the stack below `P`,
and zeroes `dst` if it returned 0 (`after_wp`). Every write is to `dst`,
`work` or the stack below `rsp` (`Frame [dR s, wR s, stkR s]`), so the
arguments, the other buffers and the return address stay as they were.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenToSplit

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm dstB Fn)
open VG.Impl.AesGcm.X86_64.OpenTo (frameRegs stArg wipeArgs wipeBody wipe after)
open VG.Impl.AesGcm.X86_64.OpenToSplit (callArgs openToSplit)
open VG.Proof.AesGcm.X86_64.OpenTo (K R Nn NL Ad AL Src L Dst Tg TL nR aR sR dR tR res kR toPost toLeak
  apart_of_disjoint stArg_ok covers_of_mem add_ofNat_sub_ofNat zeros bytesAt_zeros zeroLoop_ok)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds onePub)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Proof.AesGcm.X86_64.Gather (CallFn)

/-! ## The function called -/

/-- An instance of `vg_aes_gcm_open_split` for a key context of kind `M`,
using at most 56 bytes of stack. -/
abbrev OpenSplitFn (M : CtxMode) := CallFn (Proof.AesGcm.openSplitX86_64M M) 56

/-! ## The contract -/

section
variable (s : State)

/-- The working space, our seventh stack argument. -/
abbrev Wk : Addr := arg s 6
abbrev wR : Region := ⟨Wk s, 2560⟩
/-- Our stack arguments. -/
abbrev argR : Region := args s 7
/-- The stack below the stack pointer: our frame, the call's return address
and its 56 bytes. -/
abbrev stkR : Region := below (s.gpr .rsp) 152

end

/-- What `openToSplit` needs, for a key context of kind `M`: `open_to`'s
(`OpenTo.ToPre`), with `work`, 2560 bytes apart from the rest. -/
structure ToPreS (M : CtxMode) (s : State) : Prop where
  rd : s.rd = [kR M s, nR s, aR s, sR s, tR s, argR s]
  wr : s.wr = [dR s, wR s]
  kd : (kR M s).Disjoint (dR s)
  nd : (nR s).Disjoint (dR s)
  ad : (aR s).Disjoint (dR s)
  sd : (sR s).Disjoint (dR s)
  dt : (dR s).Disjoint (tR s)
  da : (dR s).Disjoint (argR s)
  kw : (kR M s).Disjoint (wR s)
  nw : (nR s).Disjoint (wR s)
  aw : (aR s).Disjoint (wR s)
  sw : (sR s).Disjoint (wR s)
  tw : (tR s).Disjoint (wR s)
  dw : (dR s).Disjoint (wR s)
  wa' : (wR s).Disjoint (argR s)
  rk : (ret s).Disjoint (kR M s)
  rn : (ret s).Disjoint (nR s)
  ra : (ret s).Disjoint (aR s)
  rs : (ret s).Disjoint (sR s)
  rdd : (ret s).Disjoint (dR s)
  rt : (ret s).Disjoint (tR s)
  rw : (ret s).Disjoint (wR s)
  bk : (stkR s).Disjoint (kR M s)
  bn : (stkR s).Disjoint (nR s)
  ba : (stkR s).Disjoint (aR s)
  bs : (stkR s).Disjoint (sR s)
  bd : (stkR s).Disjoint (dR s)
  bt : (stkR s).Disjoint (tR s)
  bw : (stkR s).Disjoint (wR s)
  barg : (stkR s).Disjoint (argR s)
  wk : (K s).toNat + M.len ≤ 2 ^ 64
  wn : (Nn s).toNat + NL s ≤ 2 ^ 64
  wa : (Ad s).toNat + AL s ≤ 2 ^ 64
  ws : (Src s).toNat + L s ≤ 2 ^ 64
  wd : (Dst s).toNat + L s ≤ 2 ^ 64
  wt : (Tg s).toNat + TL s ≤ 2 ^ 64
  ww : (Wk s).toNat + 2560 ≤ 2 ^ 64
  w₁ : 152 ≤ (s.gpr .rsp).toNat
  w₂ : (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64
  rounds : rounds s
  dl : (arg s 3).toNat = L s
  ok : M.ok s.mem (K s)

/-- What two runs agree on: the arguments, and whether the tag is right. -/
def toPubS (s₁ s₂ : State) : Prop := onePub 7 s₁ s₂ ∧ toLeak s₁ = toLeak s₂

/-- `openToSplit`, for a key context of kind `M`. -/
def toSK (M : CtxMode) : Contract isa where
  pre := ToPreS M
  post := toPost
  pub := toPubS

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 152 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.gpr .rsp - BitVec.ofNat 64 152

/-- Our frame, and the stack pointer in it. -/
abbrev P : Addr := Bs s + BitVec.ofNat 64 64
abbrev FR : Region := ⟨P s, 88⟩

end

/-- What `ToPreS` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (M : CtxMode) (s : State) : Prop where
  pre : ToPreS M s
  hB : s.gpr .rsp = Bs s + BitVec.ofNat 64 152
  hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 152
  lt : L s < 2 ^ 63

theorem lay {M : CtxMode} {s : State} (hs : ToPreS M s) : Lay M s := by
  have hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 152 := toNat_sub_ofNat hs.w₁
  refine ⟨hs, (BitVec.sub_add_cancel _ _).symm, hBv, ?_⟩
  rcases Nat.eq_zero_or_pos (L s) with h0 | hpos
  · rw [h0]; decide
  have a₁ := apart_of_disjoint hs.sd hpos hpos
  have a₂ := apart_of_disjoint hs.rs (show 0 < 8 by decide) hpos
  have a₃ := apart_of_disjoint hs.rdd (show 0 < 8 by decide) hpos
  have := hs.ws; have := hs.wd; have := hs.w₂
  simp only [ret, sR, dR] at a₁ a₂ a₃
  omega

/-- The regions the function writes. -/
abbrev wrs (s : State) : List Region := [dR s, wR s, stkR s]

/-- A region apart from `dst`, `work` and the stack, which nothing writes. -/
structure Kept (s : State) (r : Region) : Prop where
  d : r.Disjoint (dR s)
  w : r.Disjoint (wR s)
  k : r.Disjoint (stkR s)
  b : r.base.toNat + r.len ≤ 2 ^ 64

theorem Kept.all {s : State} {r : Region} (hk : Kept s r) : ∀ r' ∈ wrs s, r.Disjoint r' := by
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hk.d
  · exact hk.w
  · exact hk.k

/-- The memory outside `dst`, `work` and the stack, through a frame of them. -/
theorem Kept.bytes {s : State} {m : Mem} (hf : Frame (wrs s) s.mem m) {r : Region} (hk : Kept s r) :
    bytesAt m r.base r.len = bytesAt s.mem r.base r.len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf hk.all (by have := hk.b; omega)

theorem Kept.readW {s : State} {m : Mem} (hf : Frame (wrs s) s.mem m) {r : Region} (hk : Kept s r)
    {a : Addr} (ha : r.Contains a 8) : m.readW a 64 = s.mem.readW a 64 :=
  hf.readW ha hk.all (by decide)

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 152) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub (stkR s) :=
  Offset.sub_base _ h'

theorem fr_sub (s : State) : (FR s).Sub (stkR s) := stk_sub s 64 88 (by decide)

/-- A frame of the stack alone is one of what the function writes. -/
theorem frame_stk {s : State} {m m' : Mem} (h : Frame [stkR s] m m') : Frame (wrs s) m m' :=
  h.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp

namespace Lay

variable {M : CtxMode} {s : State} (h : Lay M s)
include h

theorem hBn : (Bs s).toNat + 216 ≤ 2 ^ 64 := by have := h.pre.w₂; have := h.hBv; omega

/-- The stack arguments. -/
theorem argAddr (i : Nat) : stackArgAddr s i = Bs s + BitVec.ofNat 64 (160 + 8 * i) := by
  show s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1)) = _
  rw [h.hB, Offset.add_ofNat_add_ofNat]; congr 2; omega

theorem hargR : argR s = ⟨Bs s + BitVec.ofNat 64 160, 56⟩ := by
  show (⟨stackArgAddr s 0, 8 * 7⟩ : Region) = _
  rw [h.argAddr]

theorem k_kept : Kept s (kR M s) := ⟨h.pre.kd, h.pre.kw, h.pre.bk.symm, h.pre.wk⟩
theorem n_kept : Kept s (nR s) := ⟨h.pre.nd, h.pre.nw, h.pre.bn.symm, h.pre.wn⟩
theorem a_kept : Kept s (aR s) := ⟨h.pre.ad, h.pre.aw, h.pre.ba.symm, h.pre.wa⟩
theorem s_kept : Kept s (sR s) := ⟨h.pre.sd, h.pre.sw, h.pre.bs.symm, h.pre.ws⟩
theorem t_kept : Kept s (tR s) := ⟨h.pre.dt.symm, h.pre.tw, h.pre.bt.symm, h.pre.wt⟩
theorem arg_kept : Kept s (argR s) := by
  refine ⟨h.pre.da.symm, h.pre.wa'.symm, h.pre.barg.symm, ?_⟩
  rw [h.hargR]; have := h.hBn
  show (Bs s + BitVec.ofNat 64 160).toNat + 56 ≤ 2 ^ 64
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 160) (by decide), Nat.mod_eq_of_lt (by omega)]
  omega
theorem ret_kept : Kept s (ret s) :=
  ⟨h.pre.rdd, h.pre.rw, Offset.base_disjoint_below _ (by have := h.pre.w₁; omega),
    by have := h.pre.w₂; simp only [ret]; omega⟩

/-- The stack arguments, through a frame of what the function writes. -/
theorem argW {m : Mem} (hf : Frame (wrs s) s.mem m) (i : Nat) (hi : i < 7) :
    m.readW (Bs s + BitVec.ofNat 64 (160 + 8 * i)) 64 = arg s i := by
  have hBn := h.hBn
  rw [h.arg_kept.readW hf (by rw [h.hargR]; exact Offset.contains _ (by omega) (by omega) (by omega)),
    ← h.argAddr]
  rfl

/-- The return address, through a frame of what the function writes. -/
theorem retW {m : Mem} (hf : Frame (wrs s) s.mem m) : m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 :=
  h.ret_kept.readW hf (Region.contains_self _ _)

/-- The key context's cipher and hash subkey, through a frame of what the
function writes. -/
theorem ciph_eq {m : Mem} (hf : Frame (wrs s) s.mem m) : ctxCiph m (K s) (R s) = ctxCiph s.mem (K s) (R s) := by
  have hRb : 16 * (R s + 1) ≤ 256 := by
    rcases h.pre.rounds with e | e | e <;>
      simp only [R, e] <;> decide
  have hk := h.k_kept
  simp only [ctxCiph]
  rw [Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => (hk.all r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge)))
    (by have := hk.b; have := M.ge; omega)]

theorem hk_eq {m : Mem} (hf : Frame (wrs s) s.mem m) : ctxH m (K s) = ctxH s.mem (K s) := by
  have hk := h.k_kept
  simp only [ctxH]
  exact Proof.AesGcm.X86_64.blockAt_frame hf fun r hr => (hk.all r hr).sub_left (Offset.sub_base _ (by have := M.ge; omega))

end Lay

/-! ## The push -/

section
variable (s : State)

/-- The memory after the push of our frame. -/
abbrev eM : Mem := (pushed frameRegs s).mem

theorem hP : (pushed frameRegs s).gpr .rsp = P s := by
  rw [pushed_rsp, Offset.sub_ofNat_eq _ (show 8 * frameRegs.length ≤ 152 by decide)]; rfl

theorem hPwr : (pushed frameRegs s).wr = FR s :: s.wr := by
  rw [pushed_wr, Offset.sub_ofNat_eq _ (show 8 * frameRegs.length ≤ 152 by decide)]; rfl

end

namespace Lay

variable {M : CtxMode} {s : State} (h : Lay M s)
include h

/-- The push writes only the stack. -/
theorem frame_eM : Frame (wrs s) s.mem (eM s) := by
  have := pushRegs_mem s frameRegs (by decide) (by have := h.pre.w₁; simp only [List.length_cons, List.length_nil]; omega)
  rw [Offset.sub_ofNat_eq _ (show 8 * frameRegs.length ≤ 152 by decide)] at this
  exact frame_stk (this.1.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stkR s, by simp, fr_sub s⟩)

/-- Our stack arguments are readable, from our frame's stack pointer. -/
theorem inArg {rd wr : List Region} (hrd : rd = s.rd) (d : Nat) (h₁ : 96 ≤ d) (hd : d + 8 ≤ 152) :
    InRegions (rd ++ wr) (P s + BitVec.ofNat 64 d) 8 := by
  have hBn := h.hBn
  rw [hrd, Offset.add_ofNat_add_ofNat]
  refine ⟨argR s, List.mem_append_left _ (by rw [h.pre.rd]; simp), ?_⟩
  rw [h.hargR]; exact Offset.contains _ (by omega) (by omega) (by omega)

/-- Our stack argument at `P + d`, through a frame of what the function
writes. -/
theorem argAt {m : Mem} (hf : Frame (wrs s) s.mem m) (i : Nat) (hi : i < 7) :
    m.readW (P s + BitVec.ofNat 64 (96 + 8 * i)) 64 = arg s i := by
  rw [Offset.add_ofNat_add_ofNat, show 64 + (96 + 8 * i) = 160 + 8 * i by omega]
  exact h.argW hf i hi

/-- A word of our frame is writable. -/
theorem inFr {wr : List Region} (hwr : wr = FR s :: s.wr) (d : Nat) (hd : d + 8 ≤ 88) :
    InRegions wr (P s + BitVec.ofNat 64 d) 8 := by
  have hBn := h.hBn
  rw [hwr]
  refine ⟨FR s, List.mem_cons_self .., ?_⟩
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]; omega

omit h in
/-- A write of a word of our frame keeps the frame of what the function
writes. -/
theorem frame_wFr {m : Mem} (hf : Frame (wrs s) s.mem m) (d : Nat) (hd : d + 8 ≤ 88) (v : BitVec 64) :
    Frame (wrs s) s.mem (m.writeW (P s + BitVec.ofNat 64 d) v) := by
  refine hf.writeW (r := stkR s) (by simp) v ?_
  rw [Offset.add_ofNat_add_ofNat]
  exact Offset.contains_base _ (by omega) (by omega)

/-- A word of our frame, read through a write of another. -/
theorem rApart (m : Mem) (e k : Nat) (hek : e + 8 ≤ k ∨ k + 8 ≤ e) (he : e + 8 ≤ 88) (hk : k + 8 ≤ 88)
    (w : BitVec 64) :
    (m.writeW (P s + BitVec.ofNat 64 k) w).readW (P s + BitVec.ofNat 64 e) 64 =
      m.readW (P s + BitVec.ofNat 64 e) 64 := by
  have hBn := h.hBn
  refine Frame.readW ((Frame.refl _ _).writeW (List.mem_singleton_self ⟨P s + BitVec.ofNat 64 k, 8⟩) w
    (Region.contains_self _ _)) (r := ⟨P s + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

end Lay

/-! ## The call's arguments -/

/-- A state in our frame's body, before the call. -/
structure InFrame (s c : State) : Prop where
  frame : Frame (wrs s) s.mem c.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rsp → c.gpr r = s.gpr r
  rsp : c.gpr .rsp = P s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  mx : c.mxcsr = s.mxcsr

theorem pushed_inFrame {M : CtxMode} {s : State} (h : Lay M s) : InFrame s (pushed frameRegs s) :=
  ⟨h.frame_eM, fun _ _ h₂ => pushed_gpr _ _ h₂, hP s, pushed_rd _ _, hPwr s, pushed_mxcsr _ _⟩

/-- `stArg d (96 + 8 i)`: our stack argument `i` stored in the word `d` of
our frame. -/
theorem stArgI_wp {M : CtxMode} {s c : State} (h : Lay M s) (hc : InFrame s c) (d i : Nat) (hd : d + 8 ≤ 88)
    (hi : i < 7) :
    WP isa (.block (stArg d (96 + 8 * i))) c fun e =>
      e.mem = c.mem.writeW (P s + BitVec.ofNat 64 d) (arg s i) ∧ InFrame s e := by
  refine WP.mono_mx rfl (stArg_ok c hc.rsp d (96 + 8 * i)
    (h.inArg (wr := c.wr) hc.rd _ (by omega) (by omega)) (h.inFr hc.wr d hd)) fun e ⟨me, ge, rde, wre⟩ mxe => ?_
  rw [h.argAt hc.frame i hi] at me
  exact ⟨me, me ▸ Lay.frame_wFr hc.frame d hd _, fun r h₁ h₂ => by rw [ge r h₁, hc.gpr r h₁ h₂],
    by rw [ge _ (by decide), hc.rsp], rde.trans hc.rd, wre.trans hc.wr, mxe.trans hc.mx⟩

section
variable (s : State)

/-- The words `callArgs` writes, from the memory `m`. -/
abbrev rW (m : Mem) : Mem :=
  ((((((m.writeW (P s + BitVec.ofNat 64 0) (Dst s)).writeW (P s + BitVec.ofNat 64 8) (arg s 1)).writeW
    (P s + BitVec.ofNat 64 16) (Tg s)).writeW (P s + BitVec.ofNat 64 24) (arg s 5)).writeW
    (P s + BitVec.ofNat 64 32) (Src s)).writeW (P s + BitVec.ofNat 64 40) (arg s 1)).writeW
    (P s + BitVec.ofNat 64 48) (Wk s)

end

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  infr : InFrame s c
  mem : ∃ m, c.mem = rW s m

theorem ready_wp {M : CtxMode} {s c : State} (h : Lay M s) (hc : InFrame s c) : WP isa callArgs c (Ready s) := by
  refine WP.seq (WP.mono (stArgI_wp h hc 0 2 (by decide) (by decide)) fun c₁ ⟨m₁, h₁⟩ => ?_)
  refine WP.seq (WP.mono (stArgI_wp h h₁ 8 1 (by decide) (by decide)) fun c₂ ⟨m₂, h₂⟩ => ?_)
  refine WP.seq (WP.mono (stArgI_wp h h₂ 16 4 (by decide) (by decide)) fun c₃ ⟨m₃, h₃⟩ => ?_)
  refine WP.seq (WP.mono (stArgI_wp h h₃ 24 5 (by decide) (by decide)) fun c₄ ⟨m₄, h₄⟩ => ?_)
  refine WP.seq (WP.mono (stArgI_wp h h₄ 32 0 (by decide) (by decide)) fun c₅ ⟨m₅, h₅⟩ => ?_)
  refine WP.seq (WP.mono (stArgI_wp h h₅ 40 1 (by decide) (by decide)) fun c₆ ⟨m₆, h₆⟩ => ?_)
  refine WP.mono (stArgI_wp h h₆ 48 6 (by decide) (by decide)) fun c₇ ⟨m₇, h₇⟩ => ⟨h₇, c.mem, ?_⟩
  rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]

namespace Lay

variable {M : CtxMode} {s : State} (h : Lay M s)
include h

/-- The words `callArgs` wrote. -/
theorem rArgs (m : Mem) : (rW s m).readW (P s + BitVec.ofNat 64 0) 64 = Dst s ∧
    (rW s m).readW (P s + BitVec.ofNat 64 8) 64 = arg s 1 ∧
    (rW s m).readW (P s + BitVec.ofNat 64 16) 64 = Tg s ∧ (rW s m).readW (P s + BitVec.ofNat 64 24) 64 = arg s 5 ∧
    (rW s m).readW (P s + BitVec.ofNat 64 32) 64 = Src s ∧ (rW s m).readW (P s + BitVec.ofNat 64 40) 64 = arg s 1 ∧
    (rW s m).readW (P s + BitVec.ofNat 64 48) 64 = Wk s := by
  unfold rW
  have ap (e k : Nat) (hek : e + 8 ≤ k ∨ k + 8 ≤ e) (he : e + 8 ≤ 88) (hk : k + 8 ≤ 88) :=
    fun m w => h.rApart m e k hek he hk w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [ap 0 48 (by decide) (by decide) (by decide), ap 0 40 (by decide) (by decide) (by decide),
      ap 0 32 (by decide) (by decide) (by decide), ap 0 24 (by decide) (by decide) (by decide),
      ap 0 16 (by decide) (by decide) (by decide), ap 0 8 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [ap 8 48 (by decide) (by decide) (by decide), ap 8 40 (by decide) (by decide) (by decide),
      ap 8 32 (by decide) (by decide) (by decide), ap 8 24 (by decide) (by decide) (by decide),
      ap 8 16 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [ap 16 48 (by decide) (by decide) (by decide), ap 16 40 (by decide) (by decide) (by decide),
      ap 16 32 (by decide) (by decide) (by decide), ap 16 24 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [ap 24 48 (by decide) (by decide) (by decide), ap 24 40 (by decide) (by decide) (by decide),
      ap 24 32 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [ap 32 48 (by decide) (by decide) (by decide), ap 32 40 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [ap 40 48 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _

end Lay

/-! ## The call -/

section
variable (M : CtxMode) (s c : State)

/-- The regions the call of `vg_aes_gcm_open_split` reads (with its stack
arguments, the lowest seven words of our frame) and writes. -/
abbrev rdC : List Region := [kR M s, nR s, aR s, tR s, sR s, ⟨P s, 56⟩]
abbrev wrC : List Region := [dR s, wR s]

/-- The state the callee starts in. -/
abbrev xS : State := c.callEntry.withRegions (rdC M s) (wrC s)

end

theorem xgpr_eq {M : CtxMode} {s c : State} {r : Reg} (hr : r ≠ .rsp) : (xS M s c).gpr r = c.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

section
variable {M : CtxMode} {s c : State} (h : Lay M s) (hc : Ready s c)
include h hc

omit h in
theorem Ready.xsp : (xS M s c).gpr .rsp = Bs s + BitVec.ofNat 64 56 := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.infr.rsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]

omit h in
/-- The return address of the call. -/
theorem Ready.xmem : Frame [⟨Bs s + BitVec.ofNat 64 56, 8⟩] c.mem (xS M s c).mem := by
  rw [State.withRegions_mem, State.callEntry_mem, hc.infr.rsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

omit h in
theorem Ready.xframe : Frame (wrs s) s.mem (xS M s c).mem :=
  hc.infr.frame.trans (frame_stk (hc.xmem.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stkR s, by simp, stk_sub s 56 8 (by decide)⟩))

/-- The callee's stack arguments: the lowest seven words of our frame. -/
theorem Ready.xarg (i : Nat) (hi : i < 7) :
    arg (xS M s c) i = c.mem.readW (P s + BitVec.ofNat 64 (8 * i)) 64 := by
  have hBn := h.hBn
  show (xS M s c).mem.readW ((xS M s c).gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 = _
  rw [hc.xsp, Offset.add_ofNat_add_ofNat, show 56 + 8 * (i + 1) = 64 + 8 * i by omega, ← Offset.add_ofNat_add_ofNat]
  refine Frame.readW hc.xmem (r := ⟨P s + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [Offset.add_ofNat_add_ofNat]
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

theorem Ready.xa : arg (xS M s c) 0 = Dst s ∧ arg (xS M s c) 1 = arg s 1 ∧ arg (xS M s c) 2 = Tg s ∧
    arg (xS M s c) 3 = arg s 5 ∧ arg (xS M s c) 4 = Src s ∧ arg (xS M s c) 5 = arg s 1 ∧
    arg (xS M s c) 6 = Wk s := by
  obtain ⟨m, hm⟩ := hc.mem
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, a₆⟩ := h.rArgs m
  rw [← hm] at a₀ a₁ a₂ a₃ a₄ a₅ a₆
  exact ⟨(hc.xarg h 0 (by decide)).trans a₀, (hc.xarg h 1 (by decide)).trans a₁, (hc.xarg h 2 (by decide)).trans a₂,
    (hc.xarg h 3 (by decide)).trans a₃, (hc.xarg h 4 (by decide)).trans a₄, (hc.xarg h 5 (by decide)).trans a₅,
    (hc.xarg h 6 (by decide)).trans a₆⟩

/-- What the call needs. -/
theorem Ready.callPre : (Proof.AesGcm.openSplitX86_64M M).pre (xS M s c) ∧
    Covers (rdC M s ++ wrC s) (c.rd ++ c.wr) ∧ Covers (wrC s) c.wr := by
  have hBn := h.hBn
  have hp := h.pre
  obtain ⟨xa₀, xa₁, xa₂, xa₃, xa₄, xa₅, xa₆⟩ := hc.xa h
  have hx (r : Reg) (hr : r ≠ .rsp) (ha : r ≠ .rax) : (xS M s c).gpr r = s.gpr r :=
    (xgpr_eq hr).trans (hc.infr.gpr r ha hr)
  have hxa : args (xS M s c) 7 = ⟨P s, 56⟩ := by
    show (⟨(xS M s c).gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1)), 8 * 7⟩ : Region) = _
    rw [hc.xsp, Offset.add_ofNat_add_ofNat]
  have hst (d n : Nat) (hn : n ≤ d) : below (Bs s + BitVec.ofNat 64 d) n = ⟨Bs s + BitVec.ofNat 64 (d - n), n⟩ := by
    simp only [below, add_ofNat_sub_ofNat _ hn]
  have hxsp : (Bs s + BitVec.ofNat 64 56).toNat = (Bs s).toNat + 56 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 56) (by decide), Nat.mod_eq_of_lt (by omega)]
  have sb (d n : Nat) (hd : d + n ≤ 152) {r : Region} (hr : (stkR s).Disjoint r) :
      (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := hr.sub_left (stk_sub s d n hd)
  have s0 {r : Region} (hr : (stkR s).Disjoint r) : (⟨Bs s + BitVec.ofNat 64 0, 56⟩ : Region).Disjoint r :=
    sb 0 56 (by decide) hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.AesGcm.openSplitX86_64M, Proof.AesGcm.openSplitPre, Proof.AesGcm.oneLay, State.withRegions_rd,
      State.withRegions_wr, hx .rdi (by decide) (by decide), hx .rsi (by decide) (by decide),
      hx .rdx (by decide) (by decide), hx .rcx (by decide) (by decide), hx .r8 (by decide) (by decide),
      hx .r9 (by decide) (by decide), xa₀, xa₁, xa₂, xa₃, xa₄, xa₅, xa₆, hxa, Proof.AesGcm.ret,
      Proof.AesGcm.stk56, Proof.AesGcm.stk24, hc.xsp, hst 56 56 (by decide), hst 56 24 (by decide),
      Nat.reduceSub, Proof.AesGcm.rounds]
    refine ⟨⟨trivial, trivial, ⟨hp.kd, hp.kw, hp.nd, hp.nw, hp.ad, hp.aw, hp.dw, (sb 64 56 (by decide) hp.bd).symm,
      (sb 64 56 (by decide) hp.bw).symm, sb 56 8 (by decide) hp.bd, sb 56 8 (by decide) hp.bw,
      sb 32 24 (by decide) hp.bk, sb 32 24 (by decide) hp.bn, sb 32 24 (by decide) hp.ba, sb 32 24 (by decide) hp.bd,
      sb 32 24 (by decide) hp.bw, hp.wk, hp.wn, hp.wa, hp.wd, hp.ww, by omega, by omega, hp.rounds⟩, hp.dt.symm, hp.tw,
      s0 hp.bt, hp.wt, hp.sd, hp.sw, s0 hp.bk, s0 hp.bn, s0 hp.ba, s0 hp.bs, s0 hp.bd, s0 hp.bw, hp.ws, by omega,
      trivial⟩, ?_⟩
    exact M.frame (hc.xframe (M := M)) h.k_kept.all hp.wk hp.ok
  · rw [hc.infr.rd, hc.infr.wr, hp.rd, hp.wr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact covers_of_mem (by simp)
    · exact covers_of_mem (by simp)
    · exact covers_of_mem (by simp)
    · exact covers_of_mem (by simp)
    · exact covers_of_mem (by simp)
    · intro a n ⟨x, hx', hcn⟩
      simp only [List.mem_singleton] at hx'; subst hx'
      exact ⟨FR s, by simp, by simp only [Region.Contains] at hcn ⊢; omega⟩
    · exact covers_of_mem (by simp)
    · exact covers_of_mem (by simp)
  · rw [hc.infr.wr, hp.wr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact covers_of_mem (by simp)

end

/-- What the callee computes: `openResult` on the ciphertext at `src`, which
is ours (`res`). -/
theorem Ready.xres {M : CtxMode} {s c : State} (h : Lay M s) (hc : Ready s c) :
    Proof.AesGcm.openSplitResult (xS M s c) = res s := by
  have hx (r : Reg) (hr : r ≠ .rsp) (ha : r ≠ .rax) : (xS M s c).gpr r = s.gpr r :=
    (xgpr_eq hr).trans (hc.infr.gpr r ha hr)
  obtain ⟨xa₀, xa₁, xa₂, xa₃, xa₄, xa₅, xa₆⟩ := hc.xa h
  have xf := hc.xframe (M := M)
  have en := h.n_kept.bytes xf
  have ea := h.a_kept.bytes xf
  have et := h.t_kept.bytes xf
  have es := h.s_kept.bytes xf
  simp only [nR, aR, tR, sR] at en ea et es
  simp only [Proof.AesGcm.openSplitResult, Proof.AesGcm.arg] at xa₁ xa₂ xa₃ xa₄ ⊢
  rw [xa₁, xa₂, xa₃, xa₄, hx .rdi (by decide) (by decide), hx .rsi (by decide) (by decide),
    hx .rdx (by decide) (by decide), hx .rcx (by decide) (by decide), hx .r8 (by decide) (by decide),
    hx .r9 (by decide) (by decide), h.ciph_eq xf, h.hk_eq xf, en, ea, et, es]

/-- What the callee may leak: what we may. -/
theorem Ready.leak {M : CtxMode} {s c : State} (h : Lay M s) (hc : Ready s c) :
    Proof.AesGcm.openSplitLeak (xS M s c) = toLeak s := by
  have hx : (xS M s c).gpr .rsi = s.gpr .rsi := (xgpr_eq (by decide)).trans (hc.infr.gpr _ (by decide) (by decide))
  simp only [Proof.AesGcm.openSplitLeak, toLeak, Proof.AesGcm.rounds, hc.xres h, hx]

/-- After the call: whether it succeeded, and if so the plaintext at `dst`. -/
structure Called (s z : State) : Prop where
  out : match res s with
    | some pt => (z.gpr .rax).setWidth 32 = 1 ∧ bytesAt z.mem (Dst s) (L s) = pt
    | none => (z.gpr .rax).setWidth 32 = 0
  frame : Frame (wrs s) s.mem z.mem
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → z.gpr r = s.gpr r
  rsp : z.gpr .rsp = P s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr
  mx : z.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem called_wp {M : CtxMode} (F : OpenSplitFn M) {s c : State} (h : Lay M s) (hc : Ready s c) :
    WP isa (.call F.fn.name F.fn.code) c (Called s) := by
  have hBn := h.hBn
  obtain ⟨hcp, hcov, hw⟩ := hc.callPre h
  have hd := F.xd
  refine WP.call_sp_mx F.ok F.sp (by omega) hcp hcov hw fun s' rd' wr' cs' fr' _ ⟨s₂, m₂, g₂, post'⟩ mx' => ?_
  have rsp' : s'.gpr .rsp = c.gpr .rsp := cs' .rsp (by decide)
  have hpost : (Proof.AesGcm.openSplitX86_64M M).post (xS M s c) s₂ := post'
  simp only [Proof.AesGcm.openSplitX86_64M] at hpost
  obtain ⟨xa₀, xa₁, -⟩ := hc.xa h
  rw [hc.xres h, xa₀, xa₁, m₂, g₂ .rax (by decide)] at hpost
  have fz : Frame (wrs s) s.mem s'.mem := by
    have hPs : c.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 88 := by rw [hc.infr.rsp, ← hP, pushed_rsp]; rfl
    refine hc.infr.frame.trans (fr'.sub fun r hr => ?_)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨dR s, by simp, fun _ h => h⟩
    · exact ⟨wR s, by simp, fun _ h => h⟩
    · refine ⟨stkR s, by simp, ?_⟩
      rw [hPs]
      simp only [below]
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      exact Offset.sub_below _ (by omega) (by omega)
  refine ⟨hpost, fz, fun r hr hsp => ?_, rsp'.trans hc.infr.rsp, rd'.trans hc.infr.rd, wr'.trans hc.infr.wr,
    mx'.trans (by rw [hc.infr.mx])⟩
  rw [cs' r hr]
  exact hc.infr.gpr r (by rintro rfl; simp [calleeSaved] at hr) hsp

/-! ## After the call -/

/-- At the end of our frame's body. -/
structure Done (s d : State) : Prop where
  out : toPost s d
  frame : Frame (wrs s) s.mem d.mem
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → d.gpr r = s.gpr r
  rsp : d.gpr .rsp = P s
  wr : d.wr = FR s :: s.wr
  mx : d.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

/-- After `wipeArgs`. -/
structure Wiping (s z w : State) : Prop where
  rdi : w.gpr .rdi = Dst s
  rcx : w.gpr .rcx = BitVec.ofNat 64 (L s)
  rax : w.gpr .rax = BitVec.setWidth 64 (BitVec.ofNat 32 0)
  r10 : w.gpr .r10 = BitVec.ofNat 64 0
  zf : w.zf = some (decide (0 = L s))
  gpr : ∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r10 → w.gpr r = z.gpr r
  mem : w.mem = z.mem
  rd : w.rd = z.rd
  wr : w.wr = z.wr
  mx : w.mxcsr = z.mxcsr

theorem wipeArgs_wp {M : CtxMode} {s z : State} (h : Lay M s) (hz : Called s z) :
    WP isa (.block wipeArgs) z (Wiping s z) := by
  have hBn := h.hBn
  have ia (d : Nat) (h₁ : 96 ≤ d) (hd : d + 8 ≤ 152) := h.inArg (wr := z.wr) hz.rd d h₁ hd
  obtain ⟨w, run₁, rdi₁, rcx₁, rax₁, r10₁, zf₁, g₁, m₁, rd₁, wr₁, mx₁⟩ : ∃ w, runBlock isa wipeArgs z = some w ∧
      w.gpr .rdi = z.mem.readW (P s + BitVec.ofNat 64 112) 64 ∧
      w.gpr .rcx = z.mem.readW (P s + BitVec.ofNat 64 104) 64 ∧
      w.gpr .rax = BitVec.setWidth 64 (BitVec.ofNat 32 0) ∧ w.gpr .r10 = BitVec.setWidth 64 (BitVec.ofNat 32 0) ∧
      w.zf = some (BitVec.setWidth 64 (BitVec.ofNat 32 0) - z.mem.readW (P s + BitVec.ofNat 64 104) 64 == 0) ∧
      (∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r10 → w.gpr r = z.gpr r) ∧ w.mem = z.mem ∧ w.rd = z.rd ∧
      w.wr = z.wr ∧ w.mxcsr = z.mxcsr := by
    refine ⟨_, by xrun [wipeArgs, hz.rsp, ia 104 (by decide) (by decide), ia 112 (by decide) (by decide)], ?_⟩
    refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
      by simp [gpr_setReg, gpr_arithFlags, zf_arithFlags], fun r a b c d => by simp [gpr_setReg, a, b, c, d],
      rfl, rfl, rfl, rfl⟩
  have v₁ := h.argAt hz.frame 1 (by decide)
  have v₂ := h.argAt hz.frame 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at v₁ v₂
  rw [v₂] at rdi₁
  rw [v₁] at rcx₁ zf₁
  have hlt := h.lt
  refine WP.of_runBlock ⟨w, run₁, rdi₁, by rw [rcx₁, BitVec.ofNat_toNat, BitVec.setWidth_eq], rax₁, r10₁, ?_, g₁,
    m₁, rd₁, wr₁, mx₁⟩
  rw [zf₁, show BitVec.setWidth 64 (BitVec.ofNat 32 0) = BitVec.ofNat 64 0 from rfl,
    show arg s 1 = BitVec.ofNat 64 (L s) by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
    Offset.ofNat_sub_ofNat_beq (by decide) (by omega)]

/-- `wipe`, after a call that failed. -/
theorem wipe_wp {M : CtxMode} {s z : State} (h : Lay M s) (hz : Called s z) (hres : res s = none) :
    WP isa wipe z (Done s) := by
  have hp := h.pre
  have hlt := h.lt
  have hout (m : Mem) (hm : m = writeBytes z.mem (Dst s) (zeros (L s))) (d : State) (hdm : d.mem = m)
      (hdax : d.gpr .rax = BitVec.setWidth 64 (BitVec.ofNat 32 0)) : toPost s d := by
    simp only [toPost, hres]
    exact ⟨by rw [hdax]; rfl, by rw [hdm, hm]; exact bytesAt_zeros _ _ (by omega)⟩
  have hfr (m : Mem) (hm : m = writeBytes z.mem (Dst s) (zeros (L s))) : Frame (wrs s) s.mem m := by
    rw [hm]
    refine hz.frame.trans ((writeBytes_frame (R := dR s) _ _ _ ?_).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, List.length_replicate, Nat.le_refl]
  have hcs (d : State) (hd : ∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r10 → d.gpr r = z.gpr r) :
      ∀ r ∈ calleeSaved, r ≠ .rsp → d.gpr r = s.gpr r := fun r hr hsp => by
    rw [hd r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr), hz.cs r hr hsp]
  refine WP.seq (WP.mono (wipeArgs_wp h hz) fun w ⟨rdi₁, hrcx, rax₁, r10₁, hz0, g₁, m₁, rd₁, wr₁, mx₁⟩ => ?_)
  refine WP.ite (decide (0 = L s)) (by simp only [eval, hz0]) (fun he => ?_) (fun he => ?_)
  · -- No bytes.
    have h0 : L s = 0 := (of_decide_eq_true he).symm
    refine WP.block_nil ⟨hout z.mem (by rw [h0, zeros, List.replicate_zero, writeBytes_nil]) w (by rw [m₁])
      rax₁, hfr z.mem (by rw [h0, zeros, List.replicate_zero, writeBytes_nil]) |>.trans (by rw [m₁]; exact Frame.refl _ _),
      hcs w g₁, by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hz.rsp], by rw [wr₁, hz.wr],
      by rw [mx₁, hz.mx]⟩
  · have hpos : 1 ≤ L s := by have := of_decide_eq_false he; omega
    refine WP.mono_mx (by decide +kernel) (zeroLoop_ok w rdi₁ hrcx r10₁ (by rw [rax₁]; rfl) hpos h.lt
      (covers_of_mem (by rw [wr₁, hz.wr, hp.wr]; simp)))
      fun d ⟨md, gd, rdd, wrd⟩ mxd => ?_
    have ed : ∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r10 → d.gpr r = z.gpr r :=
      fun r a b c e => by rw [gd r e, g₁ r a b c e]
    rw [m₁] at md
    exact ⟨hout _ rfl d md (by rw [gd _ (by decide), rax₁]), md ▸ hfr _ rfl, hcs d ed,
      by rw [ed _ (by decide) (by decide) (by decide) (by decide), hz.rsp], by rw [wrd, wr₁, hz.wr],
      by rw [mxd, mx₁, hz.mx]⟩

/-- `after`: `dst` wiped if the call failed. -/
theorem after_wp {M : CtxMode} {s z : State} (h : Lay M s) (hz : Called s z) : WP isa after z (Done s) := by
  obtain ⟨z₁, run₁, zf₁, g₁, m₁, rd₁, wr₁, mx₁⟩ : ∃ z₁, runBlock isa [.alu32 .test .rax (.reg .rax)] z = some z₁ ∧
      z₁.zf = some (((z.gpr .rax).setWidth 32 &&& (z.gpr .rax).setWidth 32) == 0) ∧ z₁.gpr = z.gpr ∧
      z₁.mem = z.mem ∧ z₁.rd = z.rd ∧ z₁.wr = z.wr ∧ z₁.mxcsr = z.mxcsr :=
    ⟨arithFlags z ((z.gpr .rax).setWidth 32 &&& (z.gpr .rax).setWidth 32) false false, by xrun [],
      by simp [zf_arithFlags], rfl, rfl, rfl, rfl, rfl⟩
  rw [BitVec.and_self] at zf₁
  have hz₁ : Called s z₁ :=
    ⟨by rw [g₁, m₁]; exact hz.out, m₁ ▸ hz.frame, fun r hr hsp => by rw [g₁]; exact hz.cs r hr hsp,
      by rw [g₁]; exact hz.rsp, rd₁.trans hz.rd, wr₁.trans hz.wr, by rw [mx₁]; exact hz.mx⟩
  refine WP.seq (WP.of_runBlock ⟨z₁, run₁, ?_⟩)
  refine WP.ite ((z.gpr .rax).setWidth 32 == 0) (by simp only [eval, zf₁]) (fun hb => ?_) (fun hb => ?_)
  · -- The call failed.
    have hres : res s = none := by
      have ho := hz.out
      revert ho
      generalize res s = o
      cases o with
      | none => exact fun _ => rfl
      | some pt => intro ho; rw [ho.1] at hb; exact absurd hb (by decide)
    exact wipe_wp h hz₁ hres
  · -- It succeeded.
    have ho := hz.out
    refine WP.block_nil ⟨?_, m₁ ▸ hz.frame, fun r hr hsp => by rw [g₁]; exact hz.cs r hr hsp,
      by rw [g₁]; exact hz.rsp, wr₁.trans hz.wr, by rw [mx₁]; exact hz.mx⟩
    simp only [toPost, g₁, m₁]
    revert ho
    generalize res s = o
    cases o with
    | none => intro ho; rw [ho] at hb; exact absurd hb (by decide)
    | some pt => exact fun ho => ho

/-! ## The function -/

/-- The body of our frame. -/
theorem body_wp {M : CtxMode} (F : OpenSplitFn M) {s : State} (h : Lay M s) :
    WP isa (.seq callArgs (.seq (.call F.fn.name F.fn.code) after)) (pushed frameRegs s) (Done s) := by
  refine WP.seq (WP.mono (ready_wp h (pushed_inFrame h)) fun r hr => ?_)
  exact WP.seq (WP.mono (called_wp F h hr) fun z hz => after_wp h hz)

theorem openToSplit_wp {M : CtxMode} (F : OpenSplitFn M) {s : State} (hs : ToPreS M s) :
    WP isa (openToSplit F.fn) s fun z => abiPreserved s z ∧ toPost s z := by
  have h := lay hs
  have hn : 8 * frameRegs.length ≤ (s.gpr .rsp).toNat := by
    have := hs.w₁; simp only [List.length_cons, List.length_nil]; omega
  refine WP.frame (by simp) (by decide) (by decide) hn (WP.mono (body_wp F h) fun d hd => ?_)
  refine ⟨by rw [hd.rsp, hP s], by rw [hd.wr, hPwr s], ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hsp : r = .rsp
    · subst hsp
      rw [popped_rsp, hd.rsp, Offset.add_ofNat_add_ofNat, h.hB]; rfl
    · have h11 : r ≠ .r11 := fun e => by subst e; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hsp h11, hd.cs r hr hsp]
  · rw [popped_mem]; exact h.retW hd.frame
  · rw [popped_mxcsr]; exact hd.mx
  · have := hd.out
    simp only [toPost, popped_mem, popped_gpr _ _ _ (show Reg.rax ≠ .rsp by decide) (show Reg.rax ≠ .r11 by decide)]
      at this ⊢
    exact this

end VG.Proof.AesGcm.X86_64.OpenToSplit
