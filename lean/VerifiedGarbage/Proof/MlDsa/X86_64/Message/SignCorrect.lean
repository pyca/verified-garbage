module

import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCall
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Hash
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.X86_64.Round
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Layout
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `MlDsa.X86_64.Message.Entry`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: the frame

Untrusted: everything here is checked by Lean. The frame's push of nine
registers (`rs`) holding the key, `msg`, `msg_len`, `ctx`, `ctx_len`, `sig`,
`rnd`, `scratch` and 0, then the store of `ctx_len` after the 0, give `Ctx`
(`entry_ok`); a frame whose body keeps `Ctx` returns with the permissions,
`rsp` and callee-saved registers of entry (`frame_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

/-- The values the frame's push stores, the first at `SP + 64`. -/
def Lay.vals (L : Lay) : List (BitVec 64) := [L.key, L.msg, L.len, L.ctx, L.ctxLen, L.sig, L.rnd, L.scr, 0]

theorem push_slot (B : Addr) (j : Nat) (hj : j < 9) :
    B + BitVec.ofNat 64 112 - BitVec.ofNat 64 (8 * (j + 1)) = B + BitVec.ofNat 64 40 + BitVec.ofNat 64 (64 - 8 * j) := by
  rw [add_add, Offset.sub_ofNat_eq _ (a := 8 * (j + 1)) (b := 112) (by omega_using [hj]), BitVec.add_sub_cancel]
  congr 2; omega_using [hj]

theorem push_base (B : Addr) : B + BitVec.ofNat 64 112 - BitVec.ofNat 64 (8 * 9) = B + BitVec.ofNat 64 40 := by
  have := push_slot B 8 (by omega_using []); simpa using this

theorem setWidth8 (x : BitVec 64) (_h : x.toNat < 256) : x.setWidth 8 = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- After the push of the registers `rs` holding `L.vals` and the store of
`ctx_len`: `Ctx`. -/
theorem entry_ok {L : Lay} (hL : L.Ok) {rs : List Reg} (hlen : rs.length = 9) (hrs : .rsp ∉ rs) {s : State}
    (hsp : s.gpr .rsp = L.B + BitVec.ofNat 64 112) (hrd : s.rd = L.rd) (hwr : s.wr = L.wr)
    (hv : ∀ j (hj : j < 9), s.gpr (rs[j]'(by omega_using [hlen, hj])) = L.vals[j]'(by simp [Lay.vals]; omega_using [hj]))
    (h8 : s.gpr .r8 = L.ctxLen) :
    WP isa (.block setHdr) (pushed rs s) fun t => Ctx L s.gpr s.mxcsr s.mem t ∧
      t.wr = (pushed rs s).wr ∧ t.gpr .rsp = (pushed rs s).gpr .rsp := by
  have hn : 8 * rs.length ≤ (s.gpr .rsp).toNat := by
    rw [hsp, hlen, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hL.nB
    rw [Nat.mod_eq_of_lt (a := 112) (by omega_using []), Nat.mod_eq_of_lt this]; omega_using []
  obtain ⟨hf, hw⟩ := pushRegs_mem s rs hrs hn
  have hslot : ∀ j (hj : j < 9), (pushed rs s).mem.readW (L.SP + BitVec.ofNat 64 (64 - 8 * j)) 64 =
      L.vals[j]'(by simp [Lay.vals]; omega_using [hj]) := fun j hj => by
    rw [← hv j hj, ← hw j (by omega_using [hlen, hj]), hsp, push_slot _ j hj]; rfl
  have hrsp : (pushed rs s).gpr .rsp = L.SP := by rw [pushed_rsp, hsp, hlen, push_base]
  have hwr' : (pushed rs s).wr = L.FR :: L.wr := by rw [pushed_wr, hsp, hlen, push_base, hwr]
  have hin : InRegions (pushed rs s).wr (L.SP + BitVec.ofNat 64 1) 1 :=
    ⟨L.FR, by rw [hwr']; simp, Offset.contains_base _ (by omega_using []) (by omega_using [])⟩
  have h8' : (pushed rs s).gpr .r8 = L.ctxLen := by rw [pushed_gpr _ _ (by decide), h8]
  apply WP.of_runBlock
  simp only [setHdr, fHdr, runBlock_cons, runStep_some, runBlock_nil, exec, State.store8, ea_stk, hrsp,
    Nat.reduceAdd, hin, ite_true, Option.some.injEq, exists_eq_left', h8',
    setWidth8 _ hL.ctxLt]
  -- The memory after the store.
  generalize hm : (pushed rs s).mem.writeW (L.SP + BitVec.ofNat 64 1) (BitVec.ofNat 8 L.ctxLen.toNat) = m'
  have hsep : ∀ j (hj : j < 8), m'.readW (L.SP + BitVec.ofNat 64 (64 - 8 * j)) 64 =
      (pushed rs s).mem.readW (L.SP + BitVec.ofNat 64 (64 - 8 * j)) 64 := fun j hj => by
    rw [← hm]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hj]) (by omega_using []) (by omega_using [])) (by decide)
  refine ⟨⟨by simp [hrd], hwr', hrsp, fun r hr hr' => pushed_gpr _ _ hr', by simp,
    (hsep 7 (by omega_using [])).trans (hslot 7 (by omega_using [])), (hsep 6 (by omega_using [])).trans (hslot 6 (by omega_using [])),
    (hsep 5 (by omega_using [])).trans (hslot 5 (by omega_using [])), (hsep 4 (by omega_using [])).trans (hslot 4 (by omega_using [])),
    (hsep 3 (by omega_using [])).trans (hslot 3 (by omega_using [])), (hsep 2 (by omega_using [])).trans (hslot 2 (by omega_using [])),
    (hsep 1 (by omega_using [])).trans (hslot 1 (by omega_using [])), (hsep 0 (by omega_using [])).trans (hslot 0 (by omega_using [])), ?_, ?_⟩,
    trivial, trivial⟩
  · -- The two bytes: the low byte of the pushed 0, and `ctx_len`.
    have h0 := hslot 8 (by omega_using [])
    simp only [Lay.vals, Nat.reduceMul, Nat.sub_self, BitVec.add_zero] at h0
    have b0 : (pushed rs s).mem L.SP = 0 := by
      have := Mem.extractLsb'_read (pushed rs s).mem L.SP (n := 8) (j := 0) (by omega_using [])
      simp only [BitVec.add_zero, Nat.mul_zero] at this
      rw [← this]
      have e : (pushed rs s).mem.read L.SP 8 = (pushed rs s).mem.readW L.SP 64 := by
        simp only [Mem.readW]; rfl
      rw [e, h0]; rfl
    rw [← hm]
    simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, BitVec.add_zero]
    refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
    · rw [Mem.writeW, Mem.write_apply (by
        rw [Offset.toNat_sub_add _ _ (by decide), BitVec.sub_self]; simp)]
      exact b0
    · simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.reduceDiv, Nat.lt_add_one,
        ite_true]
      ext i hi
      simp
  · show Frame [L.XS, L.STK] s.mem m'
    rw [← hm]
    have hf1 : Frame [L.STK] s.mem (pushed rs s).mem := by
      refine Frame.sub hf fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      rw [hsp, hlen, push_base]
      exact Offset.sub_base _ (by omega_using [])
    have hf2 : Frame [L.STK] s.mem ((pushed rs s).mem.writeW (L.SP + 1#64) (BitVec.ofNat 8 L.ctxLen.toNat)) :=
      hf1.writeW (List.mem_singleton_self _) _ (by
        rw [Lay.SP, add_add]; exact Offset.contains_base _ (by omega_using []) (by omega_using []))
    exact hf2.mono fun r hr => by simp at hr ⊢; exact .inr hr

end VG.Proof.MlDsa.X86_64.Message

end

end

/-!
# ML-DSA on x86-64, `sign_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`signMessageContract p X86_64.abi 112`, `signMessage n c p` returns 2 if
the context string is longer than 255 bytes; otherwise it computes `μ` of
the formatted message and calls the signing function on `μ` `c`, which
gives the signature of `ML-DSA.Sign_internal` on the formatted message
(`signMessage_correct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The branch on `ctx_len` -/

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteT hc e, q⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteF hc e, q⟩

/-- `cmp r8, 256`. -/
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .r8 (.imm 256)]) s fun s1 => s1.gpr = s.gpr ∧ s1.mem = s.mem ∧
      s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.mxcsr = s.mxcsr ∧
      isa.eval .b s1 = some (decide ((s.gpr .r8).toNat < 256)) := by
  xrun [show BitVec.signExtend 64 (256 : BitVec 32) = 256 by decide]
  exact ⟨rfl, rfl⟩

/-! ## Before the frame -/

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl

/-- `sig` to `r10`, `scratch` to `r11`, 0 to `rax`. -/
theorem signMov_ok {p : Params} {prep : Bool} {s s1 : State} (h : SPre p prep s) (hg : s1.gpr = s.gpr) (hm : s1.mem = s.mem)
    (hrd : s1.rd = s.rd) :
    WP isa (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)]) s1 fun s2 =>
      (s2.gpr .r10 = stackArg s 0 ∧ s2.gpr .r11 = stackArg s 1 ∧ s2.gpr .rax = 0 ∧ s2.mem = s.mem ∧
        s2.mxcsr = s1.mxcsr) ∧ Keep [.r10, .r11, .rax] s1 s2 := by
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (s1.rd ++ s1.wr) (s1.gpr .rsp + BitVec.ofNat 64 (8 + d)) 8 := by
    intro d hd
    refine ⟨rArgs s, by simp [hrd, h.rd], ?_⟩
    rw [hg, ← add_add, ← stackArgAddr0]
    exact Offset.contains_base _ hd (by omega_using [hd])
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  have h8 := hin 0 (by omega_using [])
  have h16 := hin 8 (by omega_using [])
  simp only [Nat.add_zero, Nat.reduceAdd] at h8 h16
  xrun [ea_stk, h8, h16, RegUpd.mxcsr_setReg]
  rw [hm, hg]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The function -/

theorem cs_r11 : ∀ r ∈ calleeSaved, r ≠ .r11 := by decide
theorem cs_tmp : ∀ r ∈ calleeSaved, r ∉ [Reg.r10, .r11, .rax] := by decide

/-- The arguments of `signRegs`, pushed. -/
theorem signRegs_vals {p : Params} {prep : Bool} {s s2 : State} (hk : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r)
    (h10 : s2.gpr .r10 = stackArg s 0) (h11 : s2.gpr .r11 = stackArg s 1) (hax : s2.gpr .rax = 0) :
    ∀ j (hj : j < 9), s2.gpr (signRegs[j]'(by simp [signRegs]; omega_using [hj])) =
      (slay p prep s).vals[j]'(by simp [Lay.vals]; omega_using [hj]) := by
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega_using [hj]
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [signRegs, Lay.vals, slay, List.getElem_cons_zero, List.getElem_cons_succ, h10, h11, hax] <;>
    exact hk _ (by decide)

/-- The postcondition of `signMessageContract` and `preparedSignMessageContract`, spelled out. -/
def SPost (p : Params) (s s' : State) : Prop :=
  match formatMessage (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) with
  | none => (s'.gpr .rax).setWidth 32 = 2
  | some M' =>
    Outcome (fun b => signInternal p b (bytesAt s.mem (s.gpr .rdi) p.skLen) M' (bytesAt s.mem (s.gpr .r9) 32))
      ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (stackArg s 0) p.sigLen)

/-- The bytes of a region apart from a frame are what they were once the
frame's bytes are lost. -/
private theorem bytes_lost {F : Region} {m m' : Mem} (f : Frame [F] m m') {p : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint F) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => lost_byte f hd (List.mem_range.mp hi)

theorem signMessage_wp {p : Params} {prep : Bool} {n : String} {c : Prog isa} (hS : SignFn p c)
    (hp : p ∈ params) {s : State} (h : SPre p prep s) :
    WP isa (signMessage n c p (flagOf prep)) s fun s' => abiPreserved s s' ∧ SPost p s s' := by
  have hK := keyLen_ge hp prep
  unfold signMessage top
  refine WP.seq (WP.mono (cmp_ok s) fun s1 ⟨hg1, hm1, hrd1, hwr1, hx1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .r8).toNat < 256
  · rw [decide_eq_true h8] at hc1
    refine wp_ite_t hc1 (WP.seq (WP.mono (signMov_ok h hg1 hm1 hrd1) fun s2 ⟨⟨h10, h11, hax, hm2, hx2⟩, k2⟩ => ?_))
    have hL := slay_ok (prep := prep) hp h h8
    have hg2 : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r := fun r hr => (k2.gpr hr).trans (by rw [hg1])
    have hsp2 : s2.gpr .rsp = (slay p prep s).B + BitVec.ofNat 64 112 := by
      rw [hg2 _ (by decide), slay_B]
    have hn : 8 * signRegs.length ≤ (s2.gpr .rsp).toNat := by
      rw [hg2 _ (by decide)]; have := h.sp; simp only [signRegs, List.length_cons, List.length_nil]; omega_using [this]
    refine WP.frame (by decide) (by decide) (by decide) hn ?_
    refine WP.seq (WP.mono (entry_ok hL rfl (by decide) hsp2 (k2.2.1.trans hrd1) (k2.2.2.trans hwr1)
      (signRegs_vals hg2 h10 h11 hax) (hg2 _ (by decide)))
      fun t ⟨hc, htw, htsp⟩ => ?_)
    have wtr : Within ⟨(slay p prep s).key + BitVec.ofNat 64 64, 64⟩ (slay p prep s).KEY :=
      within_off _ (show 64 + 64 ≤ keyLen p prep by omega_using [hK])
    refine WP.seq (WP.mono (muHash_ok hL rfl hc (tr := .slotOff fKey 64) (by decide)
      (fun t' hc' => by rw [hc'.slotOff, fKey, hc'.pKey]) ⟨_, List.mem_append_left _ hL.inKey, wtr⟩
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (Region.sub_prefix (by decide : 200 ≤ 1024)))
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)))
      ((hL.kKey.sub_left (Region.sub_prefix (by decide : 40 ≤ 112))).sub_right wtr.sub))
      fun t₁ ⟨hc₁, hf₁, hμ⟩ => ?_)
    refine WP.mono (signCall_ok hS hp h h8 hc₁ hm2.symm) fun s' ⟨hrd', hwr', hsp', hcs', hx', hf', hq⟩ => ?_
    have hm₀ : s2.mem = s.mem := hm2
    refine ⟨by rw [hsp', hc₁.rsp, ← htsp, hc.rsp], by rw [hwr', hc₁.wr, ← htw, hc.wr], fun m uk fm => ?_⟩
    -- The pop loses the frame's 72 bytes, in the stack below `rsp`, apart from
    -- the signature and the return address.
    rw [hg2 .rsp (by decide)] at fm
    obtain hF : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * signRegs.length), 8 * signRegs.length⟩ (rStk s) :=
      Offset.sub_below _ (by decide) (by decide)
    dsimp only
    refine ⟨?_, ?_⟩
    · -- The calling convention.
      refine ⟨fun r hr => ?_, ?_, ?_⟩
      · by_cases hr' : r = .rsp
        · subst hr'
          rw [popped_rsp, hsp', hc₁.rsp, Lay.SP, add_add, show 40 + 8 * signRegs.length = 112 from rfl, slay_B]
        · rw [popped_gpr _ _ _ hr' (cs_r11 r hr), hcs' r hr, hc₁.cs r hr hr', hg2 r (cs_tmp r hr)]
      · have eR : rRet s = ⟨(slay p prep s).B + BitVec.ofNat 64 112, 8⟩ := by rw [slay_B]
        have dB : ∀ k, k ≤ 112 → (rRet s).Disjoint ⟨(slay p prep s).B, k⟩ := fun k hk => by
          rw [eR]; exact Offset.disjoint_base _ hk (by have := hL.nB; omega_using [])
        rw [fm.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint_below (s.gpr .rsp) (by decide)) (by decide),
          hf'.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact h.retSig
            · exact h.retScr.sub_right (scrMu_sub p s)
            · exact dB 40 (by decide)) (by decide),
          hc₁.frame.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr.sub_right (slay_X p prep s).sub
            · exact dB 112 (by decide)) (by decide), hm₀]
      · rw [popped_mxcsr, hx', hc₁.mx, hx2, hx1]
    · unfold SPost
      rw [bytes_lost fm (h.stkSig.symm.sub_right hF)]
      rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [signInternal, messageRep, skTr]
      have ek : bytesAt t₁.mem (s.gpr .rdi) p.skLen = bytesAt s.mem (s.gpr .rdi) p.skLen := by
        rw [hc₁.bytesAt_eq (p := s.gpr .rdi) (n := p.skLen) (hL.xKey.sub_right (Region.sub_prefix hK.2.2))
          (hL.kKey.sub_right (Region.sub_prefix hK.2.2)) (by have := h.nSk; omega_using [hK]), hm₀]
      have er : bytesAt t₁.mem (s.gpr .r9) 32 = bytesAt s.mem (s.gpr .r9) 32 := by
        rw [hc₁.bytesAt_eq (p := s.gpr .r9) (n := 32) (h.rndScr.symm.sub_left (slay_X p prep s).sub) h.stkRnd (by decide), hm₀]
      have etr : bytesAt t.mem ((slay p prep s).key + BitVec.ofNat 64 64) 64 =
          ((bytesAt s.mem (s.gpr .rdi) p.skLen).drop 64).take 64 := by
        rw [hc.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide), hm₀,
          Proof.MlKem.bytesAt_slice _ _ (show 64 + 64 ≤ p.skLen by have := skLen_ge hp; omega_using [this])]
        rfl
      rw [ek, er, hμ, etr, hm₀] at hq
      simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
      exact hq
  · rw [decide_eq_false h8] at hc1
    refine wp_ite_f hc1 ?_
    xrun [show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl]
    refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, hm1], by rw [RegUpd.mxcsr_setReg, hx1]⟩, ?_⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; revert hr; decide), hg1]
    · unfold SPost
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega_using [h8])]
      rfl

theorem sPost_of {p : Params} {s s' : State} (h : SPost p s s') : (signMessageContract p X86_64.abi 112).post s s' := by
  sig_post [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  exact h

theorem sPostP_of {p : Params} {s s' : State} (h : SPost p s s') :
    (preparedSignMessageContract p X86_64.abi 112).post s s' := by
  sig_post [preparedSignMessageContract, preparedSignMessageSig, X86_64.abi, X86_64.argRegs, List.range,
    List.range.loop]
  exact h

end VG.Proof.MlDsa.X86_64.Message
