module
public import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Seal
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.TCB.X86_64.State

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops

/-! The gather caller supplies separate source and destination registers and one
stack argument. Both layout adapters invoke the same physical seal function. -/
@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Split.Compact
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (step covers_cons' covers_nil' sub_add_ofNat off_bound stackArg_entry)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

def compactContract (M : CtxMode) : Contract isa where
  pre s := BlocksTo.BT M s true true
  post s t := Proof.AesGcm.blocksPostAt (s.gpr .r10) s t
  pub a b := BlocksTo.Pub a b true

theorem callable {M : CtxMode} (T : BlocksTo.SealFn M) (s : State) (h : (compactContract M).pre s) :
    ∃ t u, Exec isa T.fn.code s t u ∧ abiPreserved s u ∧ (compactContract M).post s u := by
  obtain ⟨t,u,run,saved,post⟩ := T.wp s h
  exact ⟨t,u,run,abiPreserved_of_exec T.mx run saved,post⟩

abbrev compactReads (M : CtxMode) (Ctx SP S : Addr) (q : Nat) : List Region :=
  [⟨Ctx, M.len⟩, ⟨S, q * 16⟩, ⟨SP - BitVec.ofNat 64 8, 8⟩]

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : SealRegions M Ctx W SP D S R n sl s)
include h

omit h in
private theorem stk24_sub {SP : Addr} {a k : Nat} (ha : a ≤ 24) (hk : k ≤ a) :
    Region.Sub ⟨SP - BitVec.ofNat 64 a, k⟩ (below SP 24) := Offset.sub_below _ ha (by omega_arith)

theorem compactPre {q : Nat} (hq : 16 * q ≤ sl) {u : State}
    (hrsp : u.gpr .rsp = SP - BitVec.ofNat 64 16) (hrd : u.rd = compactReads M Ctx SP S q) (hwr : u.wr = callWr W D q)
    (h_di : u.gpr .rdi = Ctx) (h_si : u.gpr .rsi = BitVec.ofNat 64 R)
    (h_dx : u.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (h_cx : u.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (h_8 : u.gpr .r8 = S)
    (h_9 : u.gpr .r9 = BitVec.ofNat 64 q) (dst : u.gpr .r10 = D)
    (scratch : stackArg u 0 = W + BitVec.ofNat 64 448) (hok : M.ok u.mem Ctx) :
    BlocksTo.BT M u true true := by
  have L := h.lay
  have hn := h.data.ok.lt
  obtain sl64 : sl < 2 ^ 64 := by have := h.sl_le; omega_arith
  obtain hqn : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain hRn : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds.2 with h | h | h <;> subst h <;> decide)
  have sp : 24 ≤ SP.toNat := h.stackSpace
  obtain hargs : (BlocksTo.aR u true) = ⟨SP - BitVec.ofNat 64 8, 8⟩ := by
    simp only [BlocksTo.aR, BlocksTo.SP, hrsp]
    rw [sub_add_ofNat _ (by decide)]
    rfl
  obtain hret : (Proof.AesGcm.ret u) = ⟨SP - BitVec.ofNat 64 16, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  obtain hstk : (BlocksTo.tR u true) = ⟨SP - BitVec.ofNat 64 24, 8⟩ := by
    simp only [BlocksTo.tR, BlocksTo.callBytes, BlocksTo.SP, below, hrsp]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
    rfl
  obtain tA : Region.Sub ⟨SP - BitVec.ofNat 64 8, 8⟩ (below SP 24) := stk24_sub (by decide) (by decide)
  obtain tR' : Region.Sub ⟨SP - BitVec.ofNat 64 16, 8⟩ (below SP 24) := stk24_sub (by decide) (by decide)
  obtain tS : Region.Sub ⟨SP - BitVec.ofNat 64 24, 8⟩ (below SP 24) := stk24_sub (by decide) (by decide)
  obtain pr : Region.Sub ⟨S, q * 16⟩ ⟨S, sl⟩ := Region.sub_prefix (by omega_arith)
  obtain ds : Region.Sub ⟨D, q * 16⟩ ⟨D, n⟩ := Region.sub_prefix (by have := h.sl_le; omega_arith)
  obtain cW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
  obtain yW : Region.Sub (yR W) ⟨W, 2560⟩ := fun a hc => st_w a (y_sub a hc)
  obtain ws : (W + BitVec.ofNat 64 448).toNat = W.toNat + 448 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 448) (by decide)]
    have := L.ww; omega_arith
  obtain st16 : (W + BitVec.ofNat 64 16).toNat = W.toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide)]
    have := L.ww; omega_arith
  obtain st48 : (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48).toNat = W.toNat + 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 48) (by decide), st16]
    have := L.ww; omega_arith
  obtain st32 : (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16).toNat = W.toNat + 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), st16]
    have := L.ww; omega_arith
  obtain hsp16 : (SP - BitVec.ofNat 64 16).toNat = SP.toNat - 16 := toNat_sub_ofNat (by omega_arith)
  obtain dS := h.sW.sub_left pr
  obtain dD := h.data.ok.w.sub_left ds
  constructor <;> simp only [BlocksTo.kR, BlocksTo.K, BlocksTo.cR, BlocksTo.C, BlocksTo.yR, BlocksTo.Y, BlocksTo.srcR, BlocksTo.Src, BlocksTo.n, BlocksTo.wR, BlocksTo.dR, BlocksTo.Dst, BlocksTo.sR, BlocksTo.S, BlocksTo.SP, BlocksTo.argCount, ↓reduceIte, hargs, hstk, hrd, hwr, h_di, h_si, h_dx, h_cx, h_8, h_9, hqn, hRn, dst, scratch, hrsp]
  exacts [h.ext.cs.sub_right cb_sub, h.ext.cs.sub_right y_sub, h.ext.cd.sub_right ds,
    h.ext.cw.sub_right sc_w,
    Offset.disjoint _ (.inr (by decide)) (by have := L.sw; omega_arith) (by have := L.sw; omega_arith),
    (dS.sub_right cW).symm, (dD.sub_right cW).symm, (L.sb.sub_left cb_sub).sub_right sc_b,
    (h.kw.sub_right cW).symm.sub_right tA,
    (dS.sub_right yW).symm, (dD.sub_right yW).symm, (L.sb.sub_left y_sub).sub_right sc_b,
    (h.kw.sub_right yW).symm.sub_right tA,
    h.sD.imp id (fun disj => (disj.sub_left pr).sub_right ds), dS.sub_right sc_w, dD.sub_right sc_w,
    (h.kd.sub_right ds).symm.sub_right tA, (h.kw.sub_right sc_w).symm.sub_right tA,
    (h.kw.sub_left tR').sub_right cW, (h.kw.sub_left tR').sub_right yW, (h.kd.sub_left tR').sub_right ds,
    (h.kw.sub_left tR').sub_right sc_w,
    h.kM.sub_left tS, (h.kw.sub_left tS).sub_right cW, (h.kw.sub_left tS).sub_right yW,
    (h.ks.sub_left tS).sub_right pr, (h.kd.sub_left tS).sub_right ds, (h.kw.sub_left tS).sub_right sc_w,
    h.ext.w, by rw [st48]; have := L.ww; omega_arith, by rw [st32]; have := L.ww; omega_arith, by have := h.sWrap; omega_arith,
    by have := h.data.ok.wrap; have := h.sl_le; omega_arith, by rw [ws]; have := L.ww; omega_arith,
    by rw [hsp16]; omega_arith, h.rounds.2, hok]

/-- Entry state after the caller pushes scratch and the call pushes the return address. -/
abbrev compactState (M : CtxMode) (Ctx W SP D S : Addr) (q : Nat) (st : State) : State :=
  (pushed [.rax] st).callEntry.withRegions (compactReads M Ctx SP S q) (callWr W D q)

/-- The shared leaf receives its register arguments and can access precisely the supplied regions. -/
theorem compactInput {q : Nat} (hq : 16 * q ≤ sl) {st : State}
    (hsp : st.gpr .rsp = SP) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hm : st.mem = s.mem)
    (h_di : st.gpr .rdi = Ctx) (h_si : st.gpr .rsi = BitVec.ofNat 64 R)
    (h_dx : st.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = S)
    (h_9 : st.gpr .r9 = BitVec.ofNat 64 q) (h_10 : st.gpr .r10 = D)
    (h_ax : st.gpr .rax = W + BitVec.ofNat 64 448) :
    BlocksTo.BT M (compactState M Ctx W SP D S q st) true true ∧
      Covers (compactReads M Ctx SP S q ++ callWr W D q)
        ((pushed [.rax] st).rd ++ (pushed [.rax] st).wr) ∧
      Covers (callWr W D q) (pushed [.rax] st).wr ∧
      (∀ r, r ≠ .rsp → (compactState M Ctx W SP D S q st).gpr r = st.gpr r) ∧
      (compactState M Ctx W SP D S q st).gpr .rsp = SP - BitVec.ofNat 64 16 ∧
      stackArg (compactState M Ctx W SP D S q st) 0 = W + BitVec.ofNat 64 448 := by
  have L := h.lay
  have sp : 24 ≤ SP.toNat := h.stackSpace
  have hn := h.data.ok.lt
  obtain hqs : q * 16 ≤ sl := by omega_arith
  obtain hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax] (by decide) hn8
  obtain hpj' : ∀ j (hj : j < 1), (pushed [.rax] st).mem.readW (SP - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      st.gpr ([Reg.rax][j]'hj) := fun j hj => by rw [← hsp]; exact hpj j hj
  obtain hP : (pushed [.rax] st).gpr .rsp = SP - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP - BitVec.ofNat 64 8, 8⟩] st.mem (pushed [.rax] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP - BitVec.ofNat 64 16, 8⟩] (pushed [.rax] st).mem
      (pushed [.rax] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain onStack : ∀ {a k : Nat}, a ≤ 24 → k ≤ a → ∃ r ∈ [below SP 24], Region.Sub ⟨SP - BitVec.ofNat 64 a, k⟩ r :=
    fun ha hk => ⟨_, List.mem_singleton_self _, stk24_sub ha hk⟩
  obtain fS : Frame [below SP 24] st.mem (pushed [.rax] st).callEntry.mem :=
    (hpf'.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact onStack (by decide) (by decide)).trans
      (hE.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact onStack (by decide) (by decide))
  obtain hPsp8 : 8 ≤ (SP - BitVec.ofNat 64 8).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  obtain hPt : (SP - BitVec.ofNat 64 8).toNat = SP.toNat - 8 := toNat_sub_ofNat (by omega_arith)
  obtain ea : ∀ i, i < 1 → stackArg ((pushed [.rax] st).callEntry.withRegions (compactReads M Ctx SP S q)
      (callWr W D q)) i =
      (pushed [.rax] st).mem.readW (SP - BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i)) 64 :=
    fun i hi => stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega_arith)
  obtain a0 := ea 0 (by decide)
  rw [show SP - BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * 0) = SP - BitVec.ofNat 64 (8 * (0 + 1)) by simp, hpj' 0 (by decide)] at a0
  simp only [List.getElem_cons_zero] at a0
  obtain gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax] st).callEntry.withRegions (compactReads M Ctx SP S q) (callWr W D q)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain hU : ((pushed [.rax] st).callEntry.withRegions (compactReads M Ctx SP S q) (callWr W D q)).gpr .rsp =
      SP - BitVec.ofNat 64 16 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  have kM := h.kM
  obtain hok : M.ok ((pushed [.rax] st).callEntry.withRegions (compactReads M Ctx SP S q) (callWr W D q)).mem Ctx := by
    rw [State.withRegions_mem]
    exact M.frame fS (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kM.symm) h.ext.w
      (hm ▸ h.ext.ok)
  obtain hpre := compactPre h hq hU rfl rfl (by rw [gU _ (by decide)]; exact h_di) (by rw [gU _ (by decide)]; exact h_si)
    (by rw [gU _ (by decide)]; exact h_dx) (by rw [gU _ (by decide)]; exact h_cx) (by rw [gU _ (by decide)]; exact h_8)
    (by rw [gU _ (by decide)]; exact h_9) (by rw [gU _ (by decide)]; exact h_10) (a0.trans h_ax) hok
  obtain hPw : (pushed [.rax] st).wr = ⟨SP - BitVec.ofNat 64 8, 8⟩ :: s.wr := by
    rw [pushed_wr, hsp, hwr]; rfl
  obtain hPr : (pushed [.rax] st).rd = s.rd := by rw [pushed_rd, hrd]
  have perm := h.env.perm
  obtain cC : Covers [cbR W] s.wr := covers_off' perm.st (show 48 + 16 ≤ 80 by decide)
  obtain cY : Covers [yR W] s.wr := covers_off' perm.st (show 16 + 16 ≤ 80 by decide)
  obtain cSc : Covers [scR W] s.wr := covers_off' perm.w (show 448 + 2112 ≤ 2560 by decide)
  obtain cD : Covers [⟨D, q * 16⟩] s.wr := covers_pre h.data.wr (by have := h.sl_le; omega_arith)
  obtain cR : Covers [⟨S, q * 16⟩] (s.rd ++ s.wr) := covers_pre h.srcCov hqs
  have cK : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr) := h.ext.cov
  obtain cw : Covers (callWr W D q) (pushed [.rax] st).wr := by
    rw [hPw]
    exact covers_cons' (covers_tail cC) (covers_cons' (covers_tail cY) (covers_cons' (covers_tail cD)
      (covers_cons' (covers_tail cSc) covers_nil')))
  obtain cr : Covers (compactReads M Ctx SP S q ++ callWr W D q)
      ((pushed [.rax] st).rd ++ (pushed [.rax] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_ins cK) (covers_cons' (covers_ins cR)
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_right (covers_tail cC))
      (covers_cons' (covers_right (covers_tail cY)) (covers_cons' (covers_right (covers_tail cD))
      (covers_cons' (covers_right (covers_tail cSc)) covers_nil'))))))
  exact ⟨hpre, cr, cw, gU, hU, a0.trans h_ax⟩

/-- Seal the `q` whole blocks from `S` to `D`, passing only the working space on the stack. -/
theorem compactCall_ok (T : BlocksTo.SealFn M) {q : Nat} (hq : 16 * q ≤ sl) {st : State}
    (hsp : st.gpr .rsp = SP) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hm : st.mem = s.mem)
    (h_di : st.gpr .rdi = Ctx) (h_si : st.gpr .rsi = BitVec.ofNat 64 R)
    (h_dx : st.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = S)
    (h_9 : st.gpr .r9 = BitVec.ofNat 64 q) (h_10 : st.gpr .r10 = D)
    (h_ax : st.gpr .rax = W + BitVec.ofNat 64 448) :
    WP isa (.frame (.push [.rax]) (.call T.fn.name T.fn.code) (.pop .rax 1)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (callWr W D q ++ [below SP 24]) st.mem st'.mem ∧
      blocksAt st'.mem D q = ctr32 (ctxCiph s.mem Ctx R) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48))
        (blocksAt s.mem S q) ∧
      blockAt st'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        Nat.repeat inc32 q (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) ∧
      blockAt st'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
        ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) (blocksAt st'.mem D q) := by
  have L := h.lay
  have sp : 24 ≤ SP.toNat := h.stackSpace
  have hn := h.data.ok.lt
  obtain hqs : q * 16 ≤ sl := by omega_arith
  obtain hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax] (by decide) hn8
  obtain hP : (pushed [.rax] st).gpr .rsp = SP - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP - BitVec.ofNat 64 8, 8⟩] st.mem (pushed [.rax] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP - BitVec.ofNat 64 16, 8⟩] (pushed [.rax] st).mem
      (pushed [.rax] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain onStack : ∀ {a k : Nat}, a ≤ 24 → k ≤ a → ∃ r ∈ [below SP 24], Region.Sub ⟨SP - BitVec.ofNat 64 a, k⟩ r :=
    fun ha hk => ⟨_, List.mem_singleton_self _, stk24_sub ha hk⟩
  obtain fS : Frame [below SP 24] st.mem (pushed [.rax] st).callEntry.mem :=
    (hpf'.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact onStack (by decide) (by decide)).trans
      (hE.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact onStack (by decide) (by decide))
  have b24 {a k : Nat} (ha : a ≤ 24) (hk : k ≤ a) : Region.Sub ⟨SP - BitVec.ofNat 64 a, k⟩ (below SP 24) :=
    Offset.sub_below _ ha (by omega_arith)
  have kM := h.kM
  obtain ⟨hpre, cr, cw, gU, -, a0⟩ := compactInput h hq hsp hrd hwr hm h_di h_si h_dx h_cx h_8 h_9 h_10 h_ax
  -- What the push and the return address leave as it was.
  obtain keep : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint (below SP 24) → k ≤ 2 ^ 64 →
      bytesAt (pushed [.rax] st).callEntry.mem p k = bytesAt s.mem p k := fun hd hk => by
    rw [← hm]
    exact bytesAt_frame fS (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hk
  obtain keepB : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint (below SP 24) →
      blockAt (pushed [.rax] st).callEntry.mem p = blockAt s.mem p := fun hd => by
    rw [blockAt, blockAt, keep hd (by decide)]
  obtain cW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
  obtain yW : Region.Sub (yR W) ⟨W, 2560⟩ := fun a hc => st_w a (y_sub a hc)
  obtain eC := keepB ((h.kw.sub_right cW).symm)
  obtain eY := keepB ((h.kw.sub_right yW).symm)
  obtain eS : blocksAt (pushed [.rax] st).callEntry.mem S q = blocksAt s.mem S q := by
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq,
      keep ((h.ks.sub_right (Region.sub_prefix (by omega_arith))).symm) (by have := h.sWrap; omega_arith)]
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds.2 with h | h | h <;> subst h <;> decide
  obtain eK : ctxCiph (pushed [.rax] st).callEntry.mem Ctx R = ctxCiph s.mem Ctx R := by
    simp only [ctxCiph]
    rw [keep ((kM.sub_right (Region.sub_prefix (Nat.le_trans hRb M.ge))).symm) (Nat.le_trans hRb (by decide))]
  obtain eH : ctxH (pushed [.rax] st).callEntry.mem Ctx = ctxH s.mem Ctx := by
    simp only [ctxH]
    exact keepB ((kM.sub_right (Offset.sub_base _ (by have := M.ge; omega_arith))).symm)
  obtain hqn : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.sl_le; omega_arith)
  obtain hRn : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds.2 with h | h | h <;> subst h <;> decide)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := compactContract M)
    (callable T) (SpSafe.of_all T.spAll) (by have := T.xd; omega_arith) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  obtain r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [compactContract, Proof.AesGcm.blocksPostAt, gU _ (by decide : Reg.r10 ≠ .rsp), h_10,
    State.withRegions_mem, gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp),
    gU _ (by decide : Reg.rdx ≠ .rsp), gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp),
    gU _ (by decide : Reg.r9 ≠ .rsp), h_di, h_si, h_dx, h_cx, h_8, h_9, hqn, hRn, hm₂, eK, eH,
    eC, eY, eS] at hpost
  obtain ⟨o₁, o₂, o₃⟩ := hpost
  refine ⟨r₃, hwr', fun m u fm => ?_⟩
  -- The `pop` loses the frame's 24 bytes, in the stack below `SP`, apart from
  -- the outputs.
  obtain fm' : Frame [below SP 24] s'.mem m := by
    rw [hsp] at fm
    exact fm.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact onStack (by decide) (by decide)
  obtain one : ∀ {r : Region}, (below SP 24).Disjoint r → ∀ r' ∈ [below SP 24], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.symm
  obtain kD : blocksAt m D q = blocksAt s'.mem D q :=
    blocksAt_frame fm' (one (h.kd.sub_right (Region.sub_prefix (by have := h.sl_le; omega_arith))))
      (by have := h.data.ok.wrap; have := h.sl_le; omega_arith)
  obtain kC := blockAt_frame fm' (one (h.kw.sub_right cW))
  obtain kY := blockAt_frame fm' (one (h.kw.sub_right yW))
  dsimp only
  refine ⟨fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP - BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = SP
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · rw [hsp] at fm
    refine Frame.trans ?_ (fm.sub fun r hr => ⟨below SP 24, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact b24 (by decide) (by decide)⟩)
    obtain bT : Region.Sub (below ((pushed [.rax] st).gpr .rsp) (T.fn.code.x86_64Depth + 8)) (below SP 24) := by
      obtain h₁ := below_sub (sp := (pushed [.rax] st).gpr .rsp) (a := T.fn.code.x86_64Depth + 8) (b := 16)
        (by have := T.xd; omega_arith) (by decide)
      obtain e : below (SP - BitVec.ofNat 64 8) 16 = ⟨SP - BitVec.ofNat 64 24, 16⟩ := by
        simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
      rw [hP] at h₁ ⊢
      rw [e] at h₁
      exact fun a h' => b24 (by decide) (by decide) a (h₁ a h')
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below SP 24, by simp, b24 (by decide) (by decide)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨below SP 24, by simp, bT⟩
  · rw [kD]; exact o₁
  · rw [kC]; exact o₂
  · rw [kY, kD, o₁]; exact o₃

end
section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}

theorem mid2_call_wp (h : CallRegions M Ctx W SP D S R n sl σ) (T : BlocksTo.SealFn M) {s : State} (g : G₂ Ctx W SP D S R sl σ s) :
    WP isa (DirectGather.callSeal T.fn) s
      (Mid2 Ctx W SP D S R sl σ) := by
  obtain ⟨he, di, si, dx, cx, r8, r9, r10, r11, ax, m, rd, wr⟩ := g
  apply WP.seq
  refine WP.of_runBlock ⟨s.setReg .r10 D, by xrun [r11], ?_⟩
  refine WP.mono (compactCall_ok h.forSeal T (st := s.setReg .r10 D) (q := sl / 16) (by omega_arith)
    (by simpa [gpr_setReg] using he.rsp) rd wr m (by simpa [gpr_setReg] using di)
    (by simpa [gpr_setReg] using si) (by simpa [gpr_setReg] using dx) (by simpa [gpr_setReg] using cx)
    (by simpa [gpr_setReg] using r8) (by simpa [gpr_setReg] using r9) (by simp [gpr_setReg])
    (by simpa [gpr_setReg] using ax))
    fun s₃ ⟨cs₃, rd₃, wr₃, fr₃, bl₃, ct₃, y₃⟩ => ⟨he.keep (fun r hr => (cs₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])).trans (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg])) rd₃ wr₃,
      rd₃.trans rd, wr₃.trans wr, by
        rw [← m]
        exact fr₃.sub fun r hr => by
          rcases List.mem_append.mp hr with hw | hk
          · exact ⟨r, List.mem_append_left _ hw, fun _ hc => hc⟩
          · obtain rfl := List.mem_singleton.mp hk
            exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by decide) (by decide)⟩,
      bl₃, ct₃, y₃⟩

private def moved (Ctx W SP D S : Addr) (R sl : Nat) (σ t : State) : Prop :=
  ∃ x, G₂ Ctx W SP D S R sl σ x ∧ t = x.setReg .r10 D

private theorem move_ok {t : State} (g : G₂ Ctx W SP D S R sl σ t) :
    WP isa (.block [.mov .r10 (.reg .r11)]) t (moved Ctx W SP D S R sl σ) :=
  WP.of_runBlock ⟨t.setReg .r10 D, by xrun [g.2.2.2.2.2.2.2.2.1], t,g,rfl⟩

theorem call_rel (h : CallRegions M Ctx W SP D S R n sl σ) (h' : CallRegions M Ctx W SP D S R n sl σ') (T : BlocksTo.SealFn M) :
    RelCT isa (fun s₁ s₂ => G₂ Ctx W SP D S R sl σ s₁ ∧ G₂ Ctx W SP D S R sl σ' s₂)
      (DirectGather.callSeal T.fn) fun _ _ => True := by
  have hq : 16 * (sl / 16) ≤ sl := Nat.mul_div_le _ _
  have mv := (rel_taint (P := fun a b => G₂ Ctx W SP D S R sl σ a ∧ G₂ Ctx W SP D S R sl σ' b)
    [] (fun _ _ _ r hr => by cases hr) (c := .block [.mov .r10 (.reg .r11)]) ⟨_, by taint_decide⟩).wp
    (fun _ _ g => ⟨move_ok g.1,move_ok g.2⟩)
  refine RelCT.seq mv (RelCT.frame (fun _ _ g => by
    obtain ⟨_,⟨_,a,rfl⟩,⟨_,b,rfl⟩⟩ := g
    simp [gpr_setReg,a.1.rsp,b.1.rsp])
    (RelCT.callEx (k := compactContract M) (callable T) T.ct fun _ _ hab => ?_))
  obtain ⟨_, _, ⟨_,⟨s₁,g₁,rfl⟩,⟨s₂,g₂,rfl⟩⟩, rfl, rfl⟩ := hab
  have one {σ x : State} (r : CallRegions M Ctx W SP D S R n sl σ) (z : G₂ Ctx W SP D S R sl σ x) := by
    obtain ⟨he,di,si,dx,cx,r8,r9,_,_,ax,m,rd,wr⟩ := z
    exact compactInput r.forSeal hq (st := x.setReg .r10 D) (by simpa [gpr_setReg] using he.rsp)
      rd wr m (by simpa [gpr_setReg] using di) (by simpa [gpr_setReg] using si)
      (by simpa [gpr_setReg] using dx) (by simpa [gpr_setReg] using cx)
      (by simpa [gpr_setReg] using r8) (by simpa [gpr_setReg] using r9)
      (by simp [gpr_setReg]) (by simpa [gpr_setReg] using ax)
  obtain ⟨p₁, cr₁, cw₁, gu₁, sp₁, sc₁⟩ := one h g₁
  obtain ⟨p₂, cr₂, cw₂, gu₂, sp₂, sc₂⟩ := one h' g₂
  obtain ⟨he₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, _, _, _, _, _, _⟩ := g₁
  obtain ⟨he₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, _, _, _, _, _, _⟩ := g₂
  refine ⟨_,_,_,_,p₁,p₂,?_,cr₁,cw₁,cr₂,cw₂,by simp [pushed_rsp,gpr_setReg,he₁.rsp,he₂.rsp]⟩
  constructor
  all_goals first
    | exact sp₂.trans sp₁.symm
    | exact sc₂.trans sc₁.symm
    | (try simp only [BlocksTo.K, BlocksTo.C, BlocksTo.Y, BlocksTo.Src, BlocksTo.Dst, ↓reduceIte])
      rw [gu₂ _ (by decide),gu₁ _ (by decide)]
      simp only [gpr_setReg]
      first | rfl | exact di₂.trans di₁.symm | exact si₂.trans si₁.symm | exact dx₂.trans dx₁.symm
            | exact cx₂.trans cx₁.symm | exact r8₂.trans r8₁.symm | exact r9₂.trans r9₁.symm

theorem callPart_rel (h : CallInputs M Ctx W SP D S R n sl σ) (h' : CallInputs M Ctx W SP D S R n sl σ') (T : BlocksTo.SealFn M) :
    RelCT isa (fun a b => G₀ Ctx W SP sl σ a ∧ G₀ Ctx W SP sl σ' b)
      (.seq (.block SealSplit.preArgs) (DirectGather.callSeal T.fn))
      fun a b => Mid2 Ctx W SP D S R sl σ a ∧ Mid2 Ctx W SP D S R sl σ' b := by
  refine RelCT.seq (step [.r13, .r14, .r15] preArgs_check (F₁ := G₀ Ctx W SP sl σ) (F₂ := G₀ Ctx W SP sl σ')
    (fun _ _ g r hr => by
      have e₁ := g.1.1; have e₂ := g.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [e₁.r13, e₂.r13]
      · rw [e₁.r14, e₂.r14]
      · rw [e₁.r15, e₂.r15])
    (fun _ _ g => g) (fun _ g => g₂_wp h g) (fun _ g => g₂_wp h' g)) ?_
  exact (rel_wp (call_rel h.regions h'.regions T) (fun _ _ g => g) (fun _ g => mid2_call_wp h.regions T g)
    (fun _ g => mid2_call_wp h'.regions T g)).mono (fun _ _ g => g) fun _ _ g => g.2

theorem call_ok (h : CallInputs M Ctx W SP D S R n sl σ) (T : BlocksTo.SealFn M) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (ax : s.gpr .rax = BitVec.ofNat 64 (sl / 16))
    (m : s.mem = σ.mem) (rd : s.rd = σ.rd) (wr : s.wr = σ.wr) :
    WP isa (.seq (.block SealSplit.preArgs) (DirectGather.callSeal T.fn)) s (Mid2 Ctx W SP D S R sl σ) :=
  WP.seq (WP.mono (g₂_wp h ⟨he,ax,m,rd,wr⟩) fun _ g => mid2_call_wp h.regions T g)

end
end VG.Proof.AesGcm.X86_64.Split.Compact
