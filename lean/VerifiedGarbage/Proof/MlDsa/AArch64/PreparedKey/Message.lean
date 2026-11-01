module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyPre
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifySat

import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Verified

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.SignEntryTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Entry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRel
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedTopTiming
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedTable
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Args
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Pre
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Rel
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsEntry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
public import VerifiedGarbage.Spec.MlDsa.CachedVerify

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Message
open VG.Impl.MlDsa.AArch64.Message

def messageSignK (p : Params) (prepared : Bool) (A : Abi isa) : Contract isa :=
  if prepared then preparedSignMessageContract p A 64 else signMessageContract p A 64

def messageSignRd (p : Params) (prepared : Bool) (s : State) : List Region :=
  [⟨s.gpr .x0, rawSignBytes p prepared⟩, ⟨s.gpr .x1, (s.gpr .x2).toNat⟩,
    ⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨s.gpr .x5, 32⟩]

theorem message_sign_resources {p : Params} {prepared : Bool} {σ : State}
    (pre : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre σ) :
    (messageSignK p prepared abi).pre (σ.withRegions (messageSignRd p prepared σ) σ.wr) ∧
    StaticRoots 64 σ ∧ PairedRoots 64 σ ∧ σ.rd = messageSignRd p prepared σ ++ signRootRd σ := by
  cases prepared
  all_goals
    simp only [messageSignK, Bool.false_eq_true, ↓reduceIte] at pre ⊢
    sig_pre [signMessageContract, signMessageSig, preparedSignMessageContract, preparedSignMessageSig,
      abi, VG.AArch64.argRegs, Abi.withConsts, pairedSignRootConsts_eq,
      Abi.constRegions, Abi.constsHeld, TableConstants.staticNttWords_length,
      InverseTable.expandedWords_length, PairedTable.expandedWords_length, stackBelow] at pre
    obtain ⟨sp, hd, hf, hi, hp', hff, hfw, hfs, hif, hiw, his, hpf, hpw, hps,
      hfa, hia, hpa, ht, hw, d1, d2, d3, d4, d5, d6, d7, d8, d9,
      k1, k2, k3, k4, k5, k6, n1, n2, n3, n4, n5, tail⟩ := pre
    have rd := (List.take_append_drop (σ.rd.length - 3) σ.rd).symm
    rw [ht, hd] at rd
    refine ⟨?_, ⟨⟨hf, hff, ?_, hfw, hfs, hfa⟩, ⟨hi, hif, ?_, hiw, his, hia⟩⟩,
      ⟨hp', hpf, ?_, hpw, hps, hpa⟩, rd⟩
    · sig_pre [signMessageContract, signMessageSig, preparedSignMessageContract, preparedSignMessageSig,
        abi, VG.AArch64.argRegs]
      exact ⟨sp,rfl,hw,d1,d2,d3,d4,d5,d6,d7,d8,d9,
        k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,tail⟩
    · exact Covers.one ⟨⟨σ.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,
        List.mem_append_left _ (by rw [rd]; simp),Region.contains_self _ _⟩
    · exact Covers.one ⟨⟨σ.syms "VG_MLDSA_INV_FOLDED",3904⟩,
        List.mem_append_left _ (by rw [rd]; simp),Region.contains_self _ _⟩
    · exact Covers.one ⟨⟨σ.syms "VG_MLDSA_INV_PAIR",4096⟩,
        List.mem_append_left _ (by rw [rd]; simp),Region.contains_self _ _⟩

structure MessageSignFacts (p : Params) (prepared : Bool) (s : State) : Prop where
  stack : 64 ≤ s.sp.toNat
  rd : s.rd = messageSignRd p prepared s ++ signRootRd s
  wr : s.wr = [⟨s.gpr .x6,p.sigLen⟩,⟨s.gpr .x7,Message.mScrLen p⟩]
  keySig : (⟨s.gpr .x0,rawSignBytes p prepared⟩ : Region).Disjoint ⟨s.gpr .x6,p.sigLen⟩
  keyScr : (⟨s.gpr .x0,rawSignBytes p prepared⟩ : Region).Disjoint ⟨s.gpr .x7,Message.mScrLen p⟩
  msgSig : (⟨s.gpr .x1,(s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x6,p.sigLen⟩
  msgScr : (⟨s.gpr .x1,(s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x7,Message.mScrLen p⟩
  ctxSig : (⟨s.gpr .x3,(s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x6,p.sigLen⟩
  ctxScr : (⟨s.gpr .x3,(s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x7,Message.mScrLen p⟩
  rndSig : (⟨s.gpr .x5,32⟩ : Region).Disjoint ⟨s.gpr .x6,p.sigLen⟩
  rndScr : (⟨s.gpr .x5,32⟩ : Region).Disjoint ⟨s.gpr .x7,Message.mScrLen p⟩
  sigScr : (⟨s.gpr .x6,p.sigLen⟩ : Region).Disjoint ⟨s.gpr .x7,Message.mScrLen p⟩
  stkKey : (below s.sp 64).Disjoint ⟨s.gpr .x0,rawSignBytes p prepared⟩
  stkMsg : (below s.sp 64).Disjoint ⟨s.gpr .x1,(s.gpr .x2).toNat⟩
  stkCtx : (below s.sp 64).Disjoint ⟨s.gpr .x3,(s.gpr .x4).toNat⟩
  stkRnd : (below s.sp 64).Disjoint ⟨s.gpr .x5,32⟩
  stkSig : (below s.sp 64).Disjoint ⟨s.gpr .x6,p.sigLen⟩
  stkScr : (below s.sp 64).Disjoint ⟨s.gpr .x7,Message.mScrLen p⟩
  nKey : (s.gpr .x0).toNat + rawSignBytes p prepared ≤ 2 ^ 64
  nMsg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  nRnd : (s.gpr .x5).toNat + 32 ≤ 2 ^ 64
  nSig : (s.gpr .x6).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (s.gpr .x7).toNat + Message.mScrLen p ≤ 2 ^ 64

theorem message_sign_facts {p : Params} {prepared : Bool} {s : State}
    (pre : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s) :
    MessageSignFacts p prepared s := by
  have resources := message_sign_resources pre
  have h := resources.1
  cases prepared
  all_goals
    simp only [messageSignK,Bool.false_eq_true,↓reduceIte] at h
    sig_pre [signMessageContract,signMessageSig,preparedSignMessageContract,preparedSignMessageSig,
      abi,VG.AArch64.argRegs] at h
    obtain ⟨sp,_,wr,d1,d2,d3,d4,d5,d6,d7,d8,d9,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,tail⟩ := h
    have ns : (s.gpr .x7).toNat + Message.mScrLen p ≤ 2 ^ 64 := by
      first | exact tail | exact tail.1
    exact ⟨sp,resources.2.2.2,wr,d1,d2,d3,d4,d5,d6,d7,d8,d9,
      k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,ns⟩

def messageSignLay (p : Params) (prepared : Bool) (s : State) : Message.Lay :=
  { Message.slay p s with keyLen := rawSignBytes p prepared }

theorem ok3_params {p : Params} (hp : Ok3 p) : p ∈ Message.params := by
  rcases hp with rfl | rfl | rfl
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem message_sign_key_bounds {p : Params} (hp : Ok3 p) (prepared : Bool) :
    128 ≤ rawSignBytes p prepared ∧ rawSignBytes p prepared < 2 ^ 16 := by
  cases prepared <;> rcases hp with rfl | rfl | rfl <;> decide

theorem messageSignLay_X (p : Params) (prepared : Bool) (s : State) :
    Within (messageSignLay p prepared s).XS ⟨s.gpr .x7,Message.mScrLen p⟩ :=
  Message.slay_X p s

theorem message_sign_layout_ok {p : Params} (hp : Ok3 p) {prepared : Bool} {s : State}
    (h : MessageSignFacts p prepared s) (h8 : (s.gpr .x4).toNat < 256) :
    (messageSignLay p prepared s).Ok := by
  have hX := messageSignLay_X p prepared s
  have hXs := hX.sub
  have st16 : Region.Sub (below s.sp 16) (below s.sp 64) := below_sub (by decide) (by decide)
  refine ⟨h8,Message.oE_lt (ok3_params hp),message_sign_key_bounds hp prepared,
    Nat.le_trans (by decide) h.stack,
    Message.toNat_X (e := oE p) h.nScr (by rw [Message.mScr_eq]),
    ⟨⟨s.gpr .x7,Message.mScrLen p⟩,by change _ ∈ s.wr; rw [h.wr]; simp,hX⟩,
    ?_,?_,?_, h.keyScr.symm.sub_left hXs,h.msgScr.symm.sub_left hXs,
    h.ctxScr.symm.sub_left hXs,(h.stkScr.sub_left st16).sub_right hXs,
    h.stkKey.sub_left st16,h.stkMsg.sub_left st16,h.stkCtx.sub_left st16,
    h.nKey,h.nMsg,h.nCtx,?_⟩
  · change (⟨s.gpr .x0,rawSignBytes p prepared⟩ : Region) ∈ s.rd
    rw [h.rd]
    simp [messageSignRd]
  · change (⟨s.gpr .x1,(s.gpr .x2).toNat⟩ : Region) ∈ s.rd
    rw [h.rd]
    simp [messageSignRd]
  · change (⟨s.gpr .x3,(s.gpr .x4).toNat⟩ : Region) ∈ s.rd
    rw [h.rd]
    simp [messageSignRd]
  · intro R hR
    change R ∈ s.wr at hR
    rw [h.wr] at hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    have ns := h.nSig
    have nw := h.nScr
    rcases hR with rfl | rfl <;> simp only <;> omega

theorem message_sign_cache {p : Params} {prepared : Bool} {s : State}
    (pre : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s)
    (hp : prepared = true) : PreparedSecretKey p s.mem (s.gpr .x0) := by
  subst prepared
  have bare := (message_sign_resources pre).1
  simp only [messageSignK,↓reduceIte] at bare
  sig_pre [preparedSignMessageContract,preparedSignMessageSig,abi,VG.AArch64.argRegs] at bare
  exact bare.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem prepared_secret_frame {p : Params} {m m' : Mem} {key : Addr} {W : List Region}
    (h : PreparedSecretKey p m key) (hf : Frame W m m')
    (hd : ∀ R ∈ W, (⟨key,preparedSecretKeyBytes p⟩ : Region).Disjoint R)
    (hb : preparedSecretKeyBytes p < 2 ^ 32) : PreparedSecretKey p m' key := by
  have cached := prepared_secret_cache_frame h hf hd hb
  intro i hi
  have value := cached i hi
  simpa only [Offset.add_add] using value

theorem message_sign_cache_ctx {p : Params} (hp : Ok3 p) {prepared : Bool} {s t : State}
    {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (pre : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s)
    (h8 : (s.gpr .x4).toNat < 256)
    (hc : Message.Ctx (messageSignLay p prepared s) g v s.mem t)
    (hflag : prepared = true) : PreparedSecretKey p t.mem (s.gpr .x0) := by
  subst prepared
  have hL := message_sign_layout_ok hp (message_sign_facts pre) h8
  apply prepared_secret_frame (message_sign_cache pre rfl) hc.frame ?_ ?_
  · intro R hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with rfl | rfl
    · exact hL.xKey.symm
    · exact hL.kKey.symm
  · rcases hp with rfl | rfl | rfl <;> decide

theorem message_sign_regs {L : Message.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m : Mem} {t u : State} (hc : Message.Ctx L g v m t)
    (hm : ∀ da ∈ Message.signArgs,u.gpr da.1 = da.2.val t) :
    u.gpr .x0 = L.key ∧ u.gpr .x1 = L.MU ∧ u.gpr .x2 = L.rnd ∧
      u.gpr .x3 = L.sig ∧ u.gpr .x4 = L.scr := by
  have e0 := hm (.x0,.slot fKey) (by simp [Message.signArgs])
  have e1 := hm (.x1,.off oMU) (by simp [Message.signArgs])
  have e2 := hm (.x2,.slot fRnd) (by simp [Message.signArgs])
  have e3 := hm (.x3,.slot fSig) (by simp [Message.signArgs])
  have e4 := hm (.x4,.slot fScr) (by simp [Message.signArgs])
  rw [hc.slotV (f := fKey) (j := 0) rfl (by decide)] at e0
  rw [hc.off] at e1
  rw [hc.slotV (f := fRnd) (j := 5) rfl (by decide)] at e2
  rw [hc.slotV (f := fSig) (j := 6) rfl (by decide)] at e3
  rw [hc.slotV (f := fScr) (j := 7) rfl (by decide)] at e4
  simp only [Message.Lay.vals,List.getD_cons_zero,List.getD_cons_succ] at e0 e2 e3 e4
  exact ⟨e0,e1,e2,e3,e4⟩

def messageSignCallRd (p : Params) (prepared : Bool) (s : State) : List Region :=
  [⟨s.gpr .x0,rawSignBytes p prepared⟩,⟨(messageSignLay p prepared s).MU,64⟩,⟨s.gpr .x5,32⟩]

def messageSignCallWr (p : Params) (s : State) : List Region :=
  [⟨s.gpr .x6,p.sigLen⟩,⟨s.gpr .x7,Message.sScr p⟩]

theorem message_sign_call_base_pre {p : Params} (hp : Ok3 p) {prepared : Bool} {s t u : State}
    {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (pre : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s)
    (h8 : (s.gpr .x4).toNat < 256)
    (hc : Message.Ctx (messageSignLay p prepared s) g v s.mem t)
    (hm : (∀ da ∈ Message.signArgs,u.gpr da.1 = da.2.val t) ∧
      VG.Proof.MlKem.AArch64.Only (Message.signArgs.map (·.1)) t u) :
    (rawSignK p prepared abi).pre
      (u.callEntry.withRegions (messageSignCallRd p prepared s) (messageSignCallWr p s)) := by
  have h := message_sign_facts pre
  have hL := message_sign_layout_ok hp h h8
  obtain ⟨e0,e1,e2,e3,e4⟩ := message_sign_regs hc hm.1
  have scr := Message.sScr_sub p s
  have mu := (Message.mu_within p s).sub
  have nscr : (s.gpr .x7).toNat + Message.sScr p ≤ 2 ^ 64 := by
    have nS := h.nScr
    simp only [Message.mScrLen,Message.sScr,messageScratchWords] at nS ⊢
    omega
  have sp : 64 ≤ u.sp.toNat := by rw [hm.2.sp,hc.sp]; exact h.stack
  have cache : prepared = true → PreparedSecretKey p u.mem (s.gpr .x0) := by
    intro flag
    rw [hm.2.mem]
    exact message_sign_cache_ctx hp pre h8 hc flag
  have hstk {R : Region} (hd : (below s.sp 64).Disjoint R) : (below u.sp 64).Disjoint R := by
    rw [hm.2.sp,hc.sp]; exact hd
  cases prepared
  all_goals
    simp only [rawSignK,Bool.false_eq_true,↓reduceIte]
    sig_pre [signContract,signSig,preparedSignContract,preparedSignSig,abi,VG.AArch64.argRegs]
    simp only [e0,e1,e2,e3,e4,messageSignCallRd,messageSignCallWr]
    refine ⟨sp,rfl,rfl,h.keySig,h.keyScr.sub_right scr,
      h.sigScr.symm.sub_left mu,Message.mu_sScr (ok3_params hp) s,
      h.rndSig,h.rndScr.sub_right scr,h.sigScr.sub_right scr,
      hstk h.stkKey,hstk (h.stkScr.sub_right mu),hstk h.stkRnd,hstk h.stkSig,
      hstk (h.stkScr.sub_right scr),h.nKey,Message.mu_nowrap hL,h.nRnd,h.nSig,?_⟩
    first | exact nscr | exact ⟨nscr,cache rfl⟩

theorem message_sign_write_cover {p : Params} {prepared : Bool} {s t u : State}
    {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m : Mem}
    (h : MessageSignFacts p prepared s)
    (hc : Message.Ctx (messageSignLay p prepared s) g v m t)
    (o : VG.Proof.MlKem.AArch64.Only (Message.signArgs.map (·.1)) t u) :
    Covers (messageSignCallWr p s) u.wr := by
  rw [o.wr,hc.wr]
  change Covers (messageSignCallWr p s) s.wr
  refine Message.covers_of_within fun R hR => ?_
  simp only [messageSignCallWr,List.mem_cons,List.not_mem_nil,or_false] at hR
  rcases hR with rfl | rfl
  · exact ⟨_,by rw [h.wr]; simp,within_self _⟩
  · refine ⟨⟨s.gpr .x7,Message.mScrLen p⟩,by rw [h.wr]; simp,within_base _ ?_⟩
    rw [Message.mScr_eq]
    simp only [Message.sScr,oE]
    omega

theorem message_sign_call_pre {p : Params} (hp : Ok3 p) {prepared : Bool} {s t u : State}
    {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (pre : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s)
    (h8 : (s.gpr .x4).toNat < 256)
    (hc : Message.Ctx (messageSignLay p prepared s) g v s.mem t)
    (hm : (∀ da ∈ Message.signArgs,u.gpr da.1 = da.2.val t) ∧
      VG.Proof.MlKem.AArch64.Only (Message.signArgs.map (·.1)) t u)
    (hy : u.syms = t.syms) (hr : StaticRoots 64 t) (rp : PairedRoots 64 t) :
    (rawSignK p prepared (abi.withConsts pairedSignRootConsts)).pre
      (u.callEntry.withRegions (messageSignCallRd p prepared s ++ signRootRd u) (messageSignCallWr p s)) := by
  have base := message_sign_call_base_pre hp pre h8 hc hm
  obtain ⟨e0,e1,e2,_,_⟩ := message_sign_regs hc hm.1
  have pass {nm : String} {ws : List (BitVec 64)} (h : StaticTable 64 nm ws t) :
      StaticTable 64 nm ws u := by
    apply staticTable_reframe h (W := []) ?_ (by simp) hm.2.rd hm.2.wr hy ?_
    · rw [hm.2.mem]; exact Frame.refl _ _
    · rw [hm.2.sp]; exact fun _ h => h
  have root : StaticRoots 64 u := ⟨pass hr.forward,pass hr.inverse⟩
  have pair : PairedRoots 64 u := by
    apply pairedRoots_reframe rp (W := []) ?_ (by simp) hm.2.rd hm.2.wr hy ?_
    · rw [hm.2.mem]; exact Frame.refl _ _
    · rw [hm.2.sp]; exact fun _ h => h
  have cw := message_sign_write_cover (message_sign_facts pre) hc hm.2
  let rd := messageSignCallRd p prepared s ++ signRootRd u
  let wr := messageSignCallWr p s
  have rb : StaticRoots 64 (u.callEntry.withRegions rd wr) :=
    ⟨operation_table_reborrow root.forward (by simp [rd,signRootRd]) cw,
      operation_table_reborrow root.inverse (by simp [rd,signRootRd]) cw⟩
  have pb : PairedRoots 64 (u.callEntry.withRegions rd wr) :=
    operation_pair_reborrow pair (by simp [rd,signRootRd]) cw
  have er : rawSignRd p prepared (u.callEntry.withRegions rd wr) = messageSignCallRd p prepared s := by
    simp only [rawSignRd,Message.gpr_ce u (r := .x0),
      Message.gpr_ce u (r := .x1),Message.gpr_ce u (r := .x2),e0,e1,e2]
    rfl
  apply raw_sign_pre_extend ?_ rb pb ?_
  · rw [er,State.withRegions_wr,State.withRegions_withRegions]
    exact base
  · rw [er]
    rfl

structure MessageSignFn (p : Params) (prepared : Bool) (code : Prog isa) : Prop where
  ver : Verified target code (rawSignK p prepared (abi.withConsts pairedSignRootConsts))
  dle : Message.DLe 4 code

theorem message_sign_read_cover {p : Params} {prepared : Bool} {s t u : State}
    {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m : Mem}
    (h : MessageSignFacts p prepared s)
    (hc : Message.Ctx (messageSignLay p prepared s) g v m t)
    (o : VG.Proof.MlKem.AArch64.Only (Message.signArgs.map (·.1)) t u) :
    Covers (messageSignCallRd p prepared s) (u.rd ++ u.wr) := by
  rw [o.rd,o.wr,hc.rd,hc.wr]
  change Covers (messageSignCallRd p prepared s) (s.rd ++ s.wr)
  refine Message.covers_of_within fun R hR => ?_
  simp only [messageSignCallRd,List.mem_cons,List.not_mem_nil,or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact ⟨_,List.mem_append_left _ (by rw [h.rd]; simp [messageSignRd]),within_self _⟩
  · exact ⟨⟨s.gpr .x7,Message.mScrLen p⟩,List.mem_append_right _ (by rw [h.wr]; simp),
      Message.mu_within p s⟩
  · exact ⟨_,List.mem_append_left _ (by rw [h.rd]; simp [messageSignRd]),within_self _⟩

theorem message_sign_call_ok {p : Params} (hp : Ok3 p) {prepared : Bool} {s t : State}
    {g : Reg → BitVec 64} {v : VReg → BitVec 128} {n : String} {code : Prog isa}
    (hS : MessageSignFn p prepared code)
    (pre : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s)
    (h8 : (s.gpr .x4).toNat < 256)
    (hc : Message.Ctx (messageSignLay p prepared s) g v s.mem t)
    (hr : StaticRoots 64 t) (rp : PairedRoots 64 t) :
    WP isa (callA n code Message.signArgs) t fun u =>
      Message.Fin (messageSignLay p prepared s) g v u ∧
      Outcome (fun b => signMu p b (Spec.Sha3.bytesAt t.mem (s.gpr .x0) p.skLen)
        (Spec.Sha3.bytesAt t.mem (messageSignLay p prepared s).MU 64)
        (Spec.Sha3.bytesAt t.mem (s.gpr .x5) 32))
        ((u.gpr .x0).setWidth 32) (Spec.Sha3.bytesAt u.mem (s.gpr .x6) p.sigLen) := by
  have h := message_sign_facts pre
  have hL := message_sign_layout_ok hp h h8
  refine WP.seq (WP.mono_syms (Message.setArgs_ok Message.signArgs (by decide) t (hc.xOk hL))
    fun t1 ⟨hA,o⟩ hsy => ?_)
  have c1 : Message.Ctx (messageSignLay p prepared s) g v s.mem t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs (fun r hr' _ => o.gpr r (by
      simp only [Message.signArgs,List.map_cons,List.map_nil]
      exact Message.not_pres hr' _))
  obtain ⟨e0,e1,e2,e3,_⟩ := message_sign_regs hc hA
  have hpre := message_sign_call_pre hp pre h8 hc ⟨hA,o⟩ hsy hr rp
  have cw := message_sign_write_cover h hc o
  have hd := hS.dle.le
  refine WP.callFV hS.ver.1 hpre ?_ cw (fun u rdu wru spu fu csu vsu post => ?_) (by omega)
  · apply Covers.append_left
      (Covers.append_left (message_sign_read_cover h hc o) ?_) cw.right
    rw [signRootRd,hsy,o.rd,o.wr]
    exact Covers.append_left hr.forward.readable (Covers.pair hr.inverse.readable rp.readable)
  · have saved : ∀ d, d + 8 ≤ 88 →
        u.mem.readW ((messageSignLay p prepared s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
        t1.mem.readW ((messageSignLay p prepared s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 := by
      intro d hD
      apply fu.readW (Region.contains_self _ _) ?_ (by decide)
      intro R hR
      simp only [messageSignCallWr,List.cons_append,List.nil_append,List.mem_cons,
        List.not_mem_nil,or_false] at hR
      rcases hR with rfl | rfl | rfl
      · rw [VG.Offset.add_add]
        exact h.sigScr.symm.sub_left ((within_off (messageSignLay p prepared s).X
          (d := 904 + d) (n := 8) (k := 1024) (by omega)).trans (messageSignLay_X p prepared s)).sub
      · exact Message.sv_sScr (ok3_params hp) s hD
      · rw [c1.sp]
        rw [VG.Offset.add_add]
        exact (h.stkScr.symm.sub_left ((within_off (messageSignLay p prepared s).X
          (d := 904 + d) (n := 8) (k := 1024) (by omega)).trans (messageSignLay_X p prepared s)).sub).sub_right
          (below_sub (by omega) (by decide))
    refine ⟨⟨rdu.trans c1.rd,wru.trans c1.wr,spu.trans c1.sp,
      (csu .x28 (by decide) (by decide)).trans c1.x28,
      (fun r hr' h28 h30 => (csu r hr' h30).trans (c1.cs r hr' h28 h30)),
      (fun r hr' => (vsu r hr').trans (c1.vs r hr')),
      (saved 0 (by decide)).trans c1.s28,(saved 8 (by decide)).trans c1.s30⟩,?_⟩
    cases prepared
    all_goals
      simp only [rawSignK,Bool.false_eq_true,↓reduceIte] at post
      sig_post [signContract,signSig,preparedSignContract,preparedSignSig,
        abi,VG.AArch64.argRegs,Abi.withConsts] at post
      simpa only [e0,e1,e2,e3,o.mem,messageSignLay,Message.slay] using post

theorem message_sign_roots_ctx {p : Params} {prepared : Bool} {s t : State}
    {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (pre : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s)
    (hc : Message.Ctx (messageSignLay p prepared s) g v s.mem t) (hy : t.syms = s.syms) :
    StaticRoots 64 t ∧ PairedRoots 64 t := by
  have resources := message_sign_resources pre
  have h := message_sign_facts pre
  have xs := (messageSignLay_X p prepared s).sub
  have stackSub : Region.Sub (below t.sp 64) (below s.sp 64) := by
    rw [hc.sp]; exact fun _ h => h
  have pass {nm : String} {ws : List (BitVec 64)} (ht : StaticTable 64 nm ws s) :
      StaticTable 64 nm ws t := by
    apply staticTable_reframe ht hc.frame ?_ hc.rd hc.wr hy stackSub
    intro R hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with rfl | rfl
    · exact (ht.writable _ (by rw [h.wr]; simp)).sub_right xs
    · exact ht.stack.sub_right (below_sub (by decide) (by decide))
  refine ⟨⟨pass resources.2.1.forward,pass resources.2.1.inverse⟩,?_⟩
  apply pairedRoots_reframe resources.2.2.1 hc.frame ?_ hc.rd hc.wr hy stackSub
  intro R hR
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
  rcases hR with rfl | rfl
  · exact (resources.2.2.1.writable _ (by rw [h.wr]; simp)).sub_right xs
  · exact resources.2.2.1.stack.sub_right (below_sub (by decide) (by decide))

theorem message_sign_correct (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {prepared : Bool} {n : String} {code : Prog isa} (hS : MessageSignFn p prepared code)
    {s : State} (pre : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s) :
    WP isa (signMessage v.callee n code p) s fun u =>
      abiPreserved s u ∧ (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).post s u := by
  have h := message_sign_facts pre
  unfold signMessage top
  refine WP.seq (WP.mono_syms (Message.lsr_ok s) fun s1 ⟨o1,hc1⟩ hy1 => ?_)
  by_cases h8 : (s.gpr .x4).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := message_sign_layout_ok hp h h8
    refine Message.wp_ite_f hc1 (WP.seq (WP.mono_syms
      (Message.enter_ok hL rfl (by decide) rfl (o1.get .x7) (by rw [o1.sp]; rfl)
        (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .x4)
        (Message.signSaves_vals (p := p) o1) (by decide)) fun t hc hyt => ?_))
    have hsk : 128 ≤ p.skLen := by rcases hp with rfl | rfl | rfl <;> decide
    have wtr : Within ⟨(messageSignLay p prepared s).key + BitVec.ofNat 64 64,64⟩
        (messageSignLay p prepared s).KEY := within_off _ (by have := hL.hKey; omega)
    have hst : Region.Sub ⟨(messageSignLay p prepared s).ST,200⟩ (messageSignLay p prepared s).XS := by
      have := Offset.sub_base (messageSignLay p prepared s).X (d := 0) (n := 200) (k := 1024) (by decide)
      simpa only [Message.x0] using this
    refine WP.seq (WP.seq (WP.mono_syms (Message.muHash_ok v hL hc (tr := .slotOff fKey 64)
      (by decide) rfl (fun t' hc' => hc'.slotOffV 64)
      ⟨_,List.mem_append_left _ hL.inKey,wtr⟩
      ((hL.xKey.symm.sub_left wtr.sub).sub_right hst)
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)))
      (hL.kKey.sub_right wtr.sub)) fun t1 ⟨hc1,hmu⟩ hymu => ?_))
    have ctx : Message.Ctx (messageSignLay p prepared s) s1.gpr s1.v s.mem t1 := by
      simpa only [o1.mem] using hc1
    have roots := message_sign_roots_ctx pre ctx (hymu.trans (hyt.trans hy1))
    refine WP.mono (message_sign_call_ok hp hS pre h8 ctx roots.1 roots.2) fun u ⟨hf,hq⟩ => ?_
    refine WP.mono (Message.leave_ok hL hf) fun z ⟨cs,sp,vs,mem,x0,_,_⟩ => ?_
    refine ⟨⟨(fun r hr => by rw [cs r hr]; exact o1.get r (by
      simp only [List.mem_singleton]; intro e; subst r; revert hr; decide)),sp,
      (fun r hr => (vs r hr).trans (o1.vcs r hr))⟩,?_⟩
    have kp : Region.Sub ⟨s.gpr .x0,p.skLen⟩ (messageSignLay p prepared s).KEY :=
      Region.sub_prefix (by change p.skLen ≤ rawSignBytes p prepared; cases prepared <;> simp [rawSignBytes,preparedSecretKeyBytes])
    have ek : Spec.Sha3.bytesAt t1.mem (s.gpr .x0) p.skLen = Spec.Sha3.bytesAt s.mem (s.gpr .x0) p.skLen :=
      ctx.bytesAt_eq (hL.xKey.sub_right kp) (hL.kKey.sub_right kp) (by rcases hp with rfl | rfl | rfl <;> decide)
    have er : Spec.Sha3.bytesAt t1.mem (s.gpr .x5) 32 = Spec.Sha3.bytesAt s.mem (s.gpr .x5) 32 :=
      ctx.bytesAt_eq (h.rndScr.symm.sub_left (messageSignLay_X p prepared s).sub)
        (h.stkRnd.sub_left (below_sub (by decide) (by decide))) (by decide)
    have etr : Spec.Sha3.bytesAt t.mem ((messageSignLay p prepared s).key + BitVec.ofNat 64 64) 64 =
        ((Spec.Sha3.bytesAt s.mem (s.gpr .x0) p.skLen).drop 64).take 64 := by
      rw [hc.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide),o1.mem,
        VG.Proof.MlKem.bytesAt_slice _ _ (by omega)]
      rfl
    rw [ek,er,hmu,etr,o1.mem] at hq
    cases prepared
    all_goals
      simp only [messageSignK,Bool.false_eq_true,↓reduceIte]
      sig_post [signMessageContract,signMessageSig,preparedSignMessageContract,preparedSignMessageSig,
        abi,VG.AArch64.argRegs,Abi.withConsts]
      rw [formatMessage_some (by rw [VG.Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [signInternal,messageRep,skTr]
      rw [x0,mem]
      simpa only [Message.hdrBytes,VG.Proof.MlKem.bytesAt_length,List.append_assoc,
        messageSignLay,Message.slay] using hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine Message.wp_ite_t hc1 (VG.Proof.MlKem.AArch64.wp_movz
      (fun s2 o2 e2 => VG.Proof.MlKem.AArch64.wp_nil ⟨⟨?_,?_,?_⟩,?_⟩))
    · intro r hr
      have h0 : r ∉ [Reg.x0] := by intro e; obtain rfl := List.mem_singleton.mp e; revert hr; decide
      have h9 : r ∉ [Reg.x9] := by intro e; obtain rfl := List.mem_singleton.mp e; revert hr; decide
      rw [o2.get r h0,o1.get r h9]
    · rw [o2.sp,o1.sp]
    · intro r hr
      rw [o2.vcs r hr,o1.vcs r hr]
    · cases prepared
      all_goals
        simp only [messageSignK,Bool.false_eq_true,↓reduceIte]
        sig_post [signMessageContract,signMessageSig,preparedSignMessageContract,preparedSignMessageSig,
          abi,VG.AArch64.argRegs,Abi.withConsts]
        rw [formatMessage_none (by rw [VG.Proof.MlKem.bytesAt_length]; omega),e2]
        rfl

def MessageSignOK (p : Params) (prepared : Bool) (L : Message.Lay) (m : Mem) (t : State) : Prop :=
  ∃ s, (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s ∧
    (s.gpr .x4).toNat < 256 ∧ messageSignLay p prepared s = L ∧ s.mem = m ∧ t.syms = s.syms

theorem message_sign_leak_eq {p : Params} (hp : Ok3 p) {L : Message.Lay} (hL : L.Ok) (m : Mem) :
    signMessageLeak p (Spec.Sha3.bytesAt m L.key p.skLen)
      (Spec.Sha3.bytesAt m L.msg L.len.toNat) (Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat)
      (Spec.Sha3.bytesAt m L.rnd 32) =
    signLeak p (Spec.Sha3.bytesAt m L.key p.skLen)
      (H (Spec.Sha3.bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ Message.hdrBytes L ++
        Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat ++ Spec.Sha3.bytesAt m L.msg L.len.toNat) 64)
      (Spec.Sha3.bytesAt m L.rnd 32) := by
  have sk : 128 ≤ p.skLen := by rcases hp with rfl | rfl | rfl <;> decide
  rw [signMessageLeak,formatMessage_some (by rw [VG.Proof.MlKem.bytesAt_length]; exact hL.ctxLt)]
  simp only [messageRep,skTr,Message.hdrBytes,VG.Proof.MlKem.bytesAt_length,List.append_assoc]
  rw [VG.Proof.MlKem.bytesAt_slice _ _ (by omega)]

theorem message_sign_call_tr {p : Params} (hp : Ok3 p) {prepared : Bool}
    {n : String} {code : Prog isa} (hS : MessageSignFn p prepared code) (tab : Addr × Addr × Addr) :
    RelCT isa (Message.Two (Message.signI p) (fun L m t =>
      MessageSignOK p prepared L m t ∧ Message.MuOk L m t ∧ Message.Paired.rootsAt t = tab))
      (callA n code Message.signArgs) (fun _ _ => True) := by
  refine Message.Optimized.call_tr (by decide) hS.ver.1 hS.ver.2.1
    (fun L => [⟨L.key,rawSignBytes p prepared⟩,⟨L.MU,64⟩,⟨L.rnd,32⟩] ++ Message.Paired.rootPairRegions tab)
    (fun L => [⟨L.sig,p.sigLen⟩,⟨L.scr,Message.sScr p⟩])
    (fun L g v m t u hL hc phi hm => ?_)
    (fun L g1 g2 v1 v2 m1 m2 a b a1 b1 hL hi c1 c2 ph1 ph2 f1 f2 => ?_)
    (fun L g v m t hL hc phi => ?_)
  · obtain ⟨⟨s,pre,h8,rfl,em,hy⟩,_,htab⟩ := phi
    have ctx : Message.Ctx (messageSignLay p prepared s) g v s.mem t := by rw [em]; exact hc
    have roots := message_sign_roots_ctx pre ctx hy
    have hpre := message_sign_call_pre hp pre h8 ctx hm.1 hm.2 roots.1 roots.2
    have er : signRootRd u = Message.Paired.rootPairRegions tab := by
      change Message.Paired.rootPairRegions (Message.Paired.rootsAt u) = _
      rw [Message.Paired.rootsAt_syms hm.2,htab]
    simpa only [er,messageSignCallRd,messageSignCallWr,messageSignLay,Message.slay] using hpre
  · obtain ⟨s,pre,h8,rfl,_,_⟩ := ph1.1
    have facts := message_sign_facts pre
    obtain ⟨x0,x1,x2,x3,x4⟩ := message_sign_regs c1 f1.1.1
    obtain ⟨y0,y1,y2,y3,y4⟩ := message_sign_regs c2 f2.1.1
    have kp : Region.Sub (⟨s.gpr .x0,p.skLen⟩ : Region) (messageSignLay p prepared s).KEY :=
      Region.sub_prefix (by change p.skLen ≤ rawSignBytes p prepared; cases prepared <;> simp [rawSignBytes,preparedSecretKeyBytes])
    have ek : ∀ {g v m a u}, Message.Ctx (messageSignLay p prepared s) g v m a →
        Message.Moved Message.signArgs a u →
        Spec.Sha3.bytesAt u.mem (s.gpr .x0) p.skLen = Spec.Sha3.bytesAt m (s.gpr .x0) p.skLen := by
      intro g v m a u c f
      rw [f.2.mem]
      exact c.bytesAt_eq (hL.xKey.sub_right kp) (hL.kKey.sub_right kp)
        (by rcases hp with rfl | rfl | rfl <;> decide)
    have er : ∀ {g v m a u}, Message.Ctx (messageSignLay p prepared s) g v m a →
        Message.Moved Message.signArgs a u →
        Spec.Sha3.bytesAt u.mem (s.gpr .x5) 32 = Spec.Sha3.bytesAt m (s.gpr .x5) 32 := by
      intro g v m a u c f
      rw [f.2.mem]
      exact c.bytesAt_eq (facts.rndScr.symm.sub_left (messageSignLay_X p prepared s).sub)
        (facts.stkRnd.sub_left (below_sub (by decide) (by decide))) (by decide)
    have emu : ∀ {a u}, Message.Moved Message.signArgs a u →
        Spec.Sha3.bytesAt u.mem (messageSignLay p prepared s).MU 64 =
        Spec.Sha3.bytesAt a.mem (messageSignLay p prepared s).MU 64 := by
      intro a u f; rw [f.2.mem]
    have keys : ∀ q, (messageSignLay p q s).key = s.gpr .x0 := fun _ => rfl
    have rnds : ∀ q, (messageSignLay p q s).rnd = s.gpr .x5 := fun _ => rfl
    -- The two public key modes have identical leakage and pointer arguments.
    cases prepared
    all_goals
      simp only [rawSignK,Bool.false_eq_true,↓reduceIte]
      sig_pub [signContract,signSig,preparedSignContract,preparedSignSig,
        abi,VG.AArch64.argRegs,Abi.withConsts,pairedSignRootConsts_eq]
      simp only [x0,x1,x2,x3,x4,y0,y1,y2,y3,y4,keys,rnds,and_true]
      refine ⟨?_,?_,?_,?_,?_⟩
      · rw [f1.1.2.sp,f2.1.2.sp,c1.sp,c2.sp]
      · exact congrArg Prod.fst ((Message.Paired.rootsAt_syms f1.2).trans
          (ph1.2.2.trans ((Message.Paired.rootsAt_syms f2.2).trans ph2.2.2).symm))
      · exact congrArg (fun q => q.2.1) ((Message.Paired.rootsAt_syms f1.2).trans
          (ph1.2.2.trans ((Message.Paired.rootsAt_syms f2.2).trans ph2.2.2).symm))
      · exact congrArg (fun q => q.2.2) ((Message.Paired.rootsAt_syms f1.2).trans
          (ph1.2.2.trans ((Message.Paired.rootsAt_syms f2.2).trans ph2.2.2).symm))
      · rw [ek c1 f1.1,ek c2 f2.1,er c1 f1.1,er c2 f2.1,emu f1.1,emu f2.1,ph1.2.1,ph2.2.1]
        have leak := hi
        unfold Message.signI at leak
        rw [message_sign_leak_eq hp hL,message_sign_leak_eq hp hL] at leak
        exact leak
  · obtain ⟨⟨s,pre,h8,rfl,em,hy⟩,_,htab⟩ := phi
    have ctx : Message.Ctx (messageSignLay p prepared s) g v s.mem t := by rw [em]; exact hc
    have roots := message_sign_roots_ctx pre ctx hy
    have identity := VG.Proof.MlKem.AArch64.Only.refl (Message.signArgs.map (·.1)) t
    have reads := message_sign_read_cover (message_sign_facts pre) hc identity
    have writes := message_sign_write_cover (message_sign_facts pre) hc identity
    have rt : signRootRd t = Message.Paired.rootPairRegions tab := by
      change Message.Paired.rootPairRegions (Message.Paired.rootsAt t) = _
      rw [htab]
    have rcov : Covers (Message.Paired.rootPairRegions tab) (t.rd ++ t.wr) := by
      rw [← rt]
      exact Covers.append_left roots.1.forward.readable (Covers.pair roots.1.inverse.readable roots.2.readable)
    rw [hc.rd,hc.wr] at reads rcov
    rw [hc.wr] at writes
    exact ⟨Covers.append_left (Covers.append_left reads rcov) writes.right,writes⟩

theorem message_sign_body_tr {p : Params} (hp : Ok3 p) {prepared : Bool}
    (tab : Addr × Addr × Addr) (v : Proof.Sha3.AArch64.Permutation)
    {n : String} {code : Prog isa} (hS : MessageSignFn p prepared code) :
    RelCT isa (Message.Two (Message.signI p) (fun L m t => MessageSignOK p prepared L m t ∧ Message.Paired.rootsAt t = tab))
      (.seq (muHash v.callee (.slotOff fKey 64)) (callA n code Message.signArgs))
      (fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp) := by
  have side : ∀ L : Message.Lay, L.Ok →
      (∃ R ∈ L.rd ++ L.wr,Within ⟨L.key + BitVec.ofNat 64 64,64⟩ R) ∧
      (⟨L.key + BitVec.ofNat 64 64,64⟩ : Region).Disjoint ⟨L.ST,200⟩ ∧
      (⟨L.key + BitVec.ofNat 64 64,64⟩ : Region).Disjoint ⟨L.KS,640⟩ ∧
      L.STK.Disjoint ⟨L.key + BitVec.ofNat 64 64,64⟩ := by
    intro L hL
    have w : Within ⟨L.key + BitVec.ofNat 64 64,64⟩ L.KEY := within_off _ (by have := hL.hKey; omega)
    have st : Region.Sub ⟨L.ST,200⟩ L.XS := by
      simpa only [Message.x0] using Offset.sub_base L.X (d := 0) (n := 200) (k := 1024) (by decide)
    exact ⟨⟨_,List.mem_append_left _ hL.inKey,w⟩,(hL.xKey.symm.sub_left w.sub).sub_right st,
      (hL.xKey.symm.sub_left w.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)),
      hL.kKey.sub_right w.sub⟩
  let Phi := fun L m t => MessageSignOK p prepared L m t ∧ Message.Paired.rootsAt t = tab
  let Psi := fun L m t => MessageSignOK p prepared L m t ∧ Message.MuOk L m t ∧ Message.Paired.rootsAt t = tab
  have hash := Message.muHash_tr v (I := Message.signI p) (Φ := Phi) (tr := .slotOff fKey 64)
    (by decide) rfl (fun L => L.key + BitVec.ofNat 64 64) (fun L g vv m t c => c.slotOffV 64) side
  have hashed := Message.two_wp (I := Message.signI p) (Φ := Phi) (Ψ := Psi) hash
    (fun L g vv m t hL c phi => by
      obtain ⟨a,b,c',d⟩ := side L hL
      refine WP.mono_syms (Message.muHash_ok v hL c (tr := .slotOff fKey 64) (by decide) rfl
        (fun t' hc => hc.slotOffV 64) a b c' d) (fun t' ⟨ct,mu⟩ hy => ?_)
      obtain ⟨⟨s,pre,h8,eL,em,hs⟩,htab⟩ := phi
      refine ⟨ct,⟨s,pre,h8,eL,em,hy.trans hs⟩,?_,(Message.Paired.rootsAt_syms hy).trans htab⟩
      unfold Message.MuOk
      have w : Within ⟨L.key + BitVec.ofNat 64 64,64⟩ L.KEY := within_off _ (by have := hL.hKey; omega)
      rw [mu,c.bytesAt_eq (hL.xKey.sub_right w.sub) (hL.kKey.sub_right w.sub) (by decide)])
  have run : ∀ {L : Message.Lay} {g vv m t}, L.Ok → Message.Ctx L g vv m t → Phi L m t →
      WP isa (.seq (muHash v.callee (.slotOff fKey 64)) (callA n code Message.signArgs)) t
        (fun u => u.gpr .x28 = t.gpr .x28 ∧ u.sp = t.sp) := by
    intro L g vv m t hL c phi
    obtain ⟨⟨s,pre,h8,rfl,em,hy⟩,_⟩ := phi
    obtain ⟨a,b,c',d⟩ := side _ hL
    refine WP.seq (WP.mono_syms (Message.muHash_ok v hL c (tr := .slotOff fKey 64) (by decide) rfl
      (fun t' hc => hc.slotOffV 64) a b c' d) (fun t' ⟨ct,_⟩ hsy => ?_))
    have ctx : Message.Ctx (messageSignLay p prepared s) g vv s.mem t' := by rw [em]; exact ct
    have roots := message_sign_roots_ctx pre ctx (hsy.trans hy)
    exact WP.mono (message_sign_call_ok hp hS pre h8 ctx roots.1 roots.2) (fun u h =>
      ⟨h.1.x28.trans c.x28.symm,h.1.sp.trans c.sp.symm⟩)
  refine RelCT.postDep (F := fun t u => u.gpr .x28 = t.gpr .x28 ∧ u.sp = t.sp)
    (hashed.seq (message_sign_call_tr hp hS tab)) ?_ ?_
  · rintro x y ⟨L,g1,g2,v1,v2,m1,m2,hL,_,c1,c2,ph1,ph2⟩
    exact ⟨run hL c1 ph1,run hL c2 ph2⟩
  · rintro x y x' y' ⟨L,g1,g2,v1,v2,m1,m2,_,_,c1,c2,_,_⟩ fx fy
    exact ⟨by rw [fx.1,fy.1,c1.x28,c2.x28],by rw [fx.2,fy.2,c1.sp,c2.sp]⟩

theorem message_sign_pub {p : Params} {prepared : Bool} {s t : State}
    (h : (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pub s t) :
    Message.Paired.SPub p s t := by
  cases prepared
  all_goals
    simp only [messageSignK,Bool.false_eq_true,↓reduceIte] at h
    sig_pub [signMessageContract,signMessageSig,preparedSignMessageContract,preparedSignMessageSig,
      abi,VG.AArch64.argRegs,Abi.withConsts,pairedSignRootConsts_eq] at h
    obtain ⟨sp,hf,hi,hp,leak,x0,x1,x2,x3,x4,x5,x6,x7⟩ := h
    exact ⟨⟨sp,leak,x0,x1,x2,x3,x4,x5,x6,x7⟩,Prod.ext hf (Prod.ext hi hp)⟩

theorem message_sign_layout_eq {p : Params} {prepared : Bool} {s t : State}
    (hs : MessageSignFacts p prepared s) (ht : MessageSignFacts p prepared t)
    (pub : Message.Paired.SPub p s t) : messageSignLay p prepared s = messageSignLay p prepared t := by
  have hf := congrArg Prod.fst pub.roots
  have hi := congrArg (fun q => q.2.1) pub.roots
  have hp := congrArg (fun q => q.2.2) pub.roots
  simp only at hf hi hp
  have rd : s.rd = t.rd := by
    rw [hs.rd,ht.rd]
    simp only [messageSignRd,signRootRd,pub.x0,pub.x1,pub.x2,pub.x3,pub.x4,pub.x5]
    rw [hf,hi,hp]
  have wr : s.wr = t.wr := by rw [hs.wr,ht.wr,pub.x6,pub.x7]
  simp only [messageSignLay,Message.slay,pub.sp,pub.x0,pub.x1,pub.x2,pub.x3,
    pub.x4,pub.x5,pub.x6,pub.x7,rd,wr]

abbrev MessageSignRel (p : Params) (prepared : Bool) (x y : State) : Prop :=
  (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre x ∧
  (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre y ∧
  (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pub x y

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Sign (Ok3 pairedSignRootConsts)
open VG.Proof.MlDsa.AArch64.Message (Ctx Ghost ALsr ghost_step lsr_ok lsr_taint enter_ok enterS_taint
  signSaves_vals movz2_taint leave_taint signI)
open VG.Proof.MlDsa.AArch64.Message.Paired (rootsAt rootsAt_syms)
variable {p : Params} {prepared : Bool}

theorem message_sign_ct (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hS : MessageSignFn p prepared c)
    (hp : Ok3 p) :
    ConstantTime isa (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pub
      (signMessage v.callee n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s₁ ∧
      (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s₂ ∧ (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pub s₁ s₂) =
      Ghost (MessageSignRel p prepared) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signMessage top
  -- `x9 ← ctx_len >> 8`.
  have hlsr := ghost_step (P := MessageSignRel p prepared) (A := fun x a => a = x) (B := fun x a => ALsr x a ∧ a.syms=x.syms) (c := .block [.lsr .x .x9 .x4 8])
    (AArch64.taintRel [] (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨(message_sign_pub hxy.2.2).sp, by simp⟩) lsr_taint)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩), WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩)⟩
  refine RelCT.seq hlsr (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.1.2, f₂.1.2, (message_sign_pub hxy.2.2).x4]) ?_ ?_)
  · -- `ctx_len ≥ 256`: return 2.
    exact AArch64.taintRel [] (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ =>
      ⟨by rw [f₁.1.1.sp, f₂.1.1.sp]; exact (message_sign_pub hxy.2.2).sp, by simp⟩) movz2_taint
  · -- The entry.
    let A : State → State → Prop := fun x a => (ALsr x a ∧ a.syms=x.syms) ∧ isa.eval (.nonzero .x .x9) a = some false
    let B : State → State → Prop := fun x t => (x.gpr .x4).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (messageSignLay p prepared x) a.gpr a.v a.mem t ∧ t.syms=x.syms
    have hent := ghost_step (P := MessageSignRel p prepared) (A := A) (B := B) (c := .block (enter .x7 p signSaves))
      (AArch64.taintRel [.x7] (fun a b ⟨x, y, hxy, f₁, f₂⟩ => ⟨by rw [f₁.1.1.1.sp, f₂.1.1.1.sp]; exact (message_sign_pub hxy.2.2).sp,
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [f₁.1.1.1.get .x7, f₂.1.1.1.get .x7]; exact (message_sign_pub hxy.2.2).x7⟩) (enterS_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre x' → A x' a' →
            WP isa (.block (enter .x7 p signSaves)) a' (B x') := fun x' a' hx ⟨⟨⟨o, e⟩, hy⟩, ef⟩ => by
          have h8 : (x'.gpr .x4).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have hL := message_sign_layout_ok hp (message_sign_facts hx) h8
          exact WP.mono_syms (enter_ok hL rfl (by decide) rfl (o.get .x7) (by rw [o.sp]; rfl) (by rw [o.rd]; rfl)
            (by rw [o.wr]; rfl) (o.get .x4) (signSaves_vals (p := p) o) (by decide)) fun t hc hyt => ⟨h8, a', o.mem, hc, hyt.trans hy⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.1.2, ← (message_sign_pub hxy.2.2).x4, ← f₁.1.2]; exact hc⟩⟩) fun _ _ h => h) (RelCT.seq (RelCT.mono (RelCT.exists_ fun tab => message_sign_body_tr hp tab v hS) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca, sya⟩,
      ⟨h8y, b', mb, cb, syb⟩⟩ => ?_) fun _ _ h => h) (AArch64.taintRel [.x28] (fun a b h => ⟨h.2, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1⟩) leave_taint))
    have hx := message_sign_facts hxy.1
    have hy := message_sign_facts hxy.2.1
    have hpub := message_sign_pub hxy.2.2
    have e := message_sign_layout_eq hx hy hpub
    refine ⟨rootsAt x,messageSignLay p prepared x,a'.gpr,b'.gpr,a'.v,b'.v,a'.mem,b'.mem,
      message_sign_layout_ok hp hx h8x,?_,ca,e ▸ cb,
      ⟨⟨x,hxy.1,h8x,rfl,ma.symm,sya⟩,rootsAt_syms sya⟩,
      ⟨⟨y,hxy.2.1,h8y,e.symm,mb.symm,syb⟩,(rootsAt_syms syb).trans hpub.roots.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.x0, ← hpub.x1, ← hpub.x2, ← hpub.x3, ← hpub.x4, ← hpub.x5] at lk
    unfold signI
    rw [ma, mb]
    exact lk

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message

def messageSignSat (p : Params) (prepared : Bool) (m : Mem) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x80000 | .x2 => 0 | .x3 => 0x90000
    | .x4 => 0 | .x5 => 0x30000 | .x6 => 0x40000 | .x7 => 0x400000 | _ => 0
  sp := 0x1000000
  mem := m
  syms name := if name = "VG_MLDSA_NTT_EXPANDED" then 1048576 else
    if name = "VG_MLDSA_INV_FOLDED" then 1052480 else 1056384
  rd := [⟨0x10000,rawSignBytes p prepared⟩,⟨0x80000,0⟩,⟨0x90000,0⟩,⟨0x30000,32⟩,
    ⟨1048576,3904⟩,⟨1052480,3904⟩,⟨1056384,4096⟩]
  wr := [⟨0x40000,p.sigLen⟩,⟨0x400000,Message.mScrLen p⟩]

theorem messageSignSat_roots (p : Params) (hp : Ok3 p) (prepared : Bool) (m : Mem)
    (hf : ∀ i < 488, m.readW (1048576 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0)
    (hi : ∀ i < 488, m.readW (1052480 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (hp' : ∀ i < 512, m.readW (1056384 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD i 0) :
    StaticRoots 64 (messageSignSat p prepared m) ∧ PairedRoots 64 (messageSignSat p prepared m) := by
  have forward : StaticTable 64 "VG_MLDSA_NTT_EXPANDED"
      Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords (messageSignSat p prepared m) := by
    refine ⟨hf, by dsimp [messageSignSat]; decide, ?_, ?_,
      by apply Region.disjoint_of_sep; dsimp [messageSignSat]; decide,
      by dsimp [messageSignSat]⟩
    · exact Covers.one ⟨⟨1048576,3904⟩, by simp [messageSignSat], Region.contains_self _ _⟩
    · rcases hp with rfl | rfl | rfl
      all_goals
        simp only [messageSignSat,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
        exact ⟨Region.disjoint_of_sep (by decide),Region.disjoint_of_sep (by decide)⟩
  have inverse : StaticTable 64 "VG_MLDSA_INV_FOLDED"
      Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords (messageSignSat p prepared m) := by
    refine ⟨hi, by dsimp [messageSignSat]; decide, ?_, ?_,
      by apply Region.disjoint_of_sep; dsimp [messageSignSat]; decide,
      by dsimp [messageSignSat]⟩
    · exact Covers.one ⟨⟨1052480,3904⟩, by simp [messageSignSat], Region.contains_self _ _⟩
    · rcases hp with rfl | rfl | rfl
      all_goals
        simp only [messageSignSat,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
        exact ⟨Region.disjoint_of_sep (by decide),Region.disjoint_of_sep (by decide)⟩
  have pair : PairedRoots 64 (messageSignSat p prepared m) := by
    refine ⟨hp', by dsimp [messageSignSat]; decide, ?_, ?_,
      by apply Region.disjoint_of_sep; dsimp [messageSignSat]; decide,
      by dsimp [messageSignSat]⟩
    · exact Covers.one ⟨⟨1056384,4096⟩, by simp [messageSignSat], Region.contains_self _ _⟩
    · rcases hp with rfl | rfl | rfl
      all_goals
        simp only [messageSignSat,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
        exact ⟨Region.disjoint_of_sep (by decide),Region.disjoint_of_sep (by decide)⟩
  exact ⟨⟨forward,inverse⟩,pair⟩


theorem message_sign_pre_extend {p : Params} {prepared : Bool} {s : State}
    (h : (messageSignK p prepared abi).pre (s.withRegions (messageSignRd p prepared s) s.wr))
    (hr : StaticRoots 64 s) (rp : PairedRoots 64 s)
    (hd : s.rd = messageSignRd p prepared s ++ signRootRd s) :
    (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s := by
  cases prepared
  all_goals
    simp only [messageSignK,Bool.false_eq_true,↓reduceIte] at h ⊢
    sig_pre [signMessageContract,signMessageSig,preparedSignMessageContract,preparedSignMessageSig,
      abi,VG.AArch64.argRegs] at h
    sig_pre [signMessageContract,signMessageSig,preparedSignMessageContract,preparedSignMessageSig,
      abi,VG.AArch64.argRegs,Abi.withConsts,pairedSignRootConsts_eq,Abi.constRegions,Abi.constsHeld,
      TableConstants.staticNttWords_length,InverseTable.expandedWords_length,PairedTable.expandedWords_length,stackBelow]
    obtain ⟨sp,_,wr,d1,d2,d3,d4,d5,d6,d7,d8,d9,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,tail⟩ := h
    exact ⟨sp,by rw [hd]; rfl,hr.forward.held,hr.inverse.held,rp.held,
      hr.forward.fit,hr.forward.writable,hr.forward.stack,hr.inverse.fit,hr.inverse.writable,hr.inverse.stack,
      rp.fit,rp.writable,rp.stack,hr.forward.aligned,hr.inverse.aligned,rp.aligned,by rw [hd]; rfl,
      wr,d1,d2,d3,d4,d5,d6,d7,d8,d9,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,tail⟩

theorem messageSignSat_pre {p : Params} (hp : Ok3 p) (prepared : Bool) (m : Mem)
    (hf : ∀ i < 488,m.readW (1048576 + BitVec.ofNat 64 (8 * i)) 64 = Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0)
    (hi : ∀ i < 488,m.readW (1052480 + BitVec.ofNat 64 (8 * i)) 64 = Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (hp' : ∀ i < 512,m.readW (1056384 + BitVec.ofNat 64 (8 * i)) 64 = Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD i 0)
    (cache : PreparedSecretKey p m 0x10000) :
    (messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre (messageSignSat p prepared m) := by
  have roots := messageSignSat_roots p hp prepared m hf hi hp'
  apply message_sign_pre_extend ?_ roots.1 roots.2 rfl
  cases prepared
  all_goals
    rcases hp with rfl | rfl | rfl
    all_goals
      simp only [messageSignK,Bool.false_eq_true,↓reduceIte]
      sig_pre [signMessageContract,signMessageSig,preparedSignMessageContract,preparedSignMessageSig,
        abi,VG.AArch64.argRegs]
      simp only [messageSignRd,rawSignBytes,Bool.false_eq_true,↓reduceIte]
      simp only [messageSignSat]
      sig_and_intros
      all_goals first | exact cache | exact Region.disjoint_of_sep (by decide) | decide +kernel

theorem message_sign_sat {p : Params} (hp : Ok3 p) (prepared : Bool) :
    ∃ s,(messageSignK p prepared (abi.withConsts pairedSignRootConsts)).pre s := by
  have roots := pairedRoots_entry (by decide) (pairedSign_sat hp)
  let m := (pairedSignSat p).mem
  obtain ⟨_,t,he,_,post⟩ := secret_correct hp (prepSecretWithTables p m) (prepSecretWithTables_pre hp m)
  sig_post [prepareSecretKeyContract,prepareSecretKeySig,abi,VG.AArch64.argRegs] at post
  have forward := secret_preparation_preserves_roots hp he (base := 1048576) (.inl rfl)
  have inverse := secret_preparation_preserves_roots hp he (base := 1052480) (.inr (.inl rfl))
  have pair := secret_preparation_preserves_roots hp he (base := 1056384) (.inr (.inr rfl))
  exact ⟨messageSignSat p prepared t.mem,messageSignSat_pre hp prepared t.mem
    (fun i hi' => (forward i (by omega)).trans (roots.2.1.forward.held i hi'))
    (fun i hi' => (inverse i (by omega)).trans (roots.2.1.inverse.held i hi'))
    (fun i hi' => (pair i hi').trans (roots.2.2.held i hi')) post.2⟩

theorem message_sign_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {prepared : Bool} {n : String} {code : Prog isa} (hS : MessageSignFn p prepared code) :
    Verified target (signMessage v.callee n code p)
      (messageSignK p prepared (abi.withConsts pairedSignRootConsts)) :=
  ⟨(fun _ h => let ⟨tr,t,he,ha,hq⟩ := message_sign_correct v hp hS h; ⟨tr,t,he,ha,hq⟩),
    message_sign_ct v hS hp,message_sign_sat hp prepared⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.AArch64.Sign

def signCode (v : Proof.Sha3.AArch64.Permutation) (p : Params) (name : String)
    (prepared : Bool) : Prog isa :=
  Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
    (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p) p prepared

theorem message_sign_fn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    (name : String) (prepared : Bool) : MessageSignFn p prepared (signCode v p name prepared) := by
  refine ⟨sign_entry_verified v hp name prepared,⟨?_⟩⟩
  have hd := (sign_withCache_dle v hp).le
  simpa only [signCode,Impl.MlDsa.AArch64.PreparedKey.Sign.entry,
    Code.aarch64Depth,Instr.frameUnits,Nat.zero_max] using Nat.add_le_add_right hd 1

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Message
open VG.Spec.Sha3 (bytesAt)

def messageVerifyK (p : Params) (prepared : Bool) (A : Abi isa) : Contract isa :=
  if prepared then preparedVerifyMessageContract p A 64 else verifyMessageCachedContract p A 64

def messageVerifyRd (p : Params) (prepared : Bool) (s : State) : List Region :=
  [⟨s.gpr .x0,rawVerifyBytes p prepared⟩,⟨s.gpr .x1,(s.gpr .x2).toNat⟩,
    ⟨s.gpr .x3,(s.gpr .x4).toNat⟩,⟨s.gpr .x5,p.sigLen⟩,⟨s.gpr .x7,64⟩]

structure MessageVerifyFacts (p : Params) (prepared : Bool) (s : State) : Prop where
  stack : 64 ≤ s.sp.toNat
  reads : ∀ R ∈ messageVerifyRd p prepared s, R ∈ s.rd
  wr : s.wr = [⟨s.gpr .x6,mScrLen p⟩]
  keyScr : (⟨s.gpr .x0,rawVerifyBytes p prepared⟩ : Region).Disjoint ⟨s.gpr .x6,mScrLen p⟩
  msgScr : (⟨s.gpr .x1,(s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x6,mScrLen p⟩
  ctxScr : (⟨s.gpr .x3,(s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x6,mScrLen p⟩
  sigScr : (⟨s.gpr .x5,p.sigLen⟩ : Region).Disjoint ⟨s.gpr .x6,mScrLen p⟩
  trScr : (⟨s.gpr .x7,64⟩ : Region).Disjoint ⟨s.gpr .x6,mScrLen p⟩
  stkKey : (below s.sp 64).Disjoint ⟨s.gpr .x0,rawVerifyBytes p prepared⟩
  stkMsg : (below s.sp 64).Disjoint ⟨s.gpr .x1,(s.gpr .x2).toNat⟩
  stkCtx : (below s.sp 64).Disjoint ⟨s.gpr .x3,(s.gpr .x4).toNat⟩
  stkSig : (below s.sp 64).Disjoint ⟨s.gpr .x5,p.sigLen⟩
  stkScr : (below s.sp 64).Disjoint ⟨s.gpr .x6,mScrLen p⟩
  stkTr : (below s.sp 64).Disjoint ⟨s.gpr .x7,64⟩
  nKey : (s.gpr .x0).toNat + rawVerifyBytes p prepared ≤ 2^64
  nMsg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2^64
  nCtx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2^64
  nSig : (s.gpr .x5).toNat + p.sigLen ≤ 2^64
  nScr : (s.gpr .x6).toNat + mScrLen p ≤ 2^64
  nTr : (s.gpr .x7).toNat + 64 ≤ 2^64
  digest : bytesAt s.mem (s.gpr .x7) 64 = pkTr (bytesAt s.mem (s.gpr .x0) p.pkLen)

theorem message_verify_facts {p : Params} {prepared : Bool} {s : State}
    (pre : (messageVerifyK p prepared abi).pre s) : MessageVerifyFacts p prepared s := by
  cases prepared
  all_goals
    simp only [messageVerifyK,Bool.false_eq_true,↓reduceIte] at pre
    sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
      abi,VG.AArch64.argRegs] at pre
    obtain ⟨sp,rd,wr,d1,d2,d3,d4,d5,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,n6,tail⟩ := pre
    exact ⟨sp,(fun R hR => rd ▸ hR),wr,d1,d2,d3,d4,d5.symm,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,n6,by first | exact tail | exact tail.2⟩

def messageVerifyLay (p : Params) (prepared : Bool) (s : State) : Message.Lay :=
  { Optimized.CachedVerify.cachedLay p s with keyLen := rawVerifyBytes p prepared }

theorem message_verify_key_bounds {p : Params} (hp : Ok3 p) (prepared : Bool) :
    128 ≤ rawVerifyBytes p prepared ∧ rawVerifyBytes p prepared < 2^16 := by
  cases prepared <;> rcases hp with rfl | rfl | rfl <;> decide

theorem messageVerifyLay_X (p : Params) (prepared : Bool) (s : State) :
    Within (messageVerifyLay p prepared s).XS ⟨s.gpr .x6,mScrLen p⟩ :=
  Optimized.CachedVerify.cachedLay_X p s

theorem message_verify_layout_ok {p : Params} (hp : Ok3 p) {prepared : Bool} {s : State}
    (h : MessageVerifyFacts p prepared s) (h8 : (s.gpr .x4).toNat < 256) :
    (messageVerifyLay p prepared s).Ok := by
  have hX := messageVerifyLay_X p prepared s
  have st16 : Region.Sub (below s.sp 16) (below s.sp 64) := below_sub (by decide) (by decide)
  refine ⟨h8,oE_lt (ok3_params hp),message_verify_key_bounds hp prepared,
    Nat.le_trans (by decide) h.stack,
    toNat_X (e := oE p) h.nScr (by rw [mScr_eq]),
    ⟨⟨s.gpr .x6,mScrLen p⟩,by change _ ∈ s.wr; rw [h.wr]; simp,hX⟩,
    ?_,?_,?_,h.keyScr.symm.sub_left hX.sub,h.msgScr.symm.sub_left hX.sub,
    h.ctxScr.symm.sub_left hX.sub,(h.stkScr.sub_left st16).sub_right hX.sub,
    h.stkKey.sub_left st16,h.stkMsg.sub_left st16,h.stkCtx.sub_left st16,
    h.nKey,h.nMsg,h.nCtx,?_⟩
  · change (⟨s.gpr .x0,rawVerifyBytes p prepared⟩ : Region) ∈ s.rd
    exact h.reads _ (by simp [messageVerifyRd])
  · change (⟨s.gpr .x1,(s.gpr .x2).toNat⟩ : Region) ∈ s.rd
    exact h.reads _ (by simp [messageVerifyRd])
  · change (⟨s.gpr .x3,(s.gpr .x4).toNat⟩ : Region) ∈ s.rd
    exact h.reads _ (by simp [messageVerifyRd])
  · intro R hR
    change R ∈ s.wr at hR
    rw [h.wr] at hR
    obtain rfl := List.mem_singleton.mp hR
    have ns := h.nScr
    simp only
    omega

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Message
open VG.Spec.Sha3 (bytesAt)

theorem prepared_public_frame {p : Params} {m m' : Mem} {key : Addr} {W : List Region}
    (h : PreparedPublicKey p m key) (hf : Frame W m m')
    (hd : ∀ R ∈ W, (⟨key,preparedPublicKeyBytes p⟩ : Region).Disjoint R)
    (hb : preparedPublicKeyBytes p < 2 ^ 32) : PreparedPublicKey p m' key := by
  have cached := prepared_public_cache_frame h hf hd hb
  intro i hi
  have value := cached i hi
  simpa only [Offset.add_add] using value

theorem message_verify_cache {p : Params} {s : State}
    (pre : (messageVerifyK p true abi).pre s) : PreparedPublicKey p s.mem (s.gpr .x0) := by
  simp only [messageVerifyK,↓reduceIte] at pre
  sig_pre [preparedVerifyMessageContract,preparedVerifyMessageSig,abi,VG.AArch64.argRegs] at pre
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,tail⟩ := pre
  exact tail.1

theorem message_verify_regs {L : Message.Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m : Mem} {t u : State} (hc : Ctx L g v m t)
    (hm : ∀ da ∈ verifyArgs,u.gpr da.1 = da.2.val t) :
    u.gpr .x0 = L.key ∧ u.gpr .x1 = L.MU ∧ u.gpr .x2 = L.sig ∧ u.gpr .x3 = L.scr := by
  have e0 := hm (.x0,.slot fKey) (by simp [verifyArgs])
  have e1 := hm (.x1,.off oMU) (by simp [verifyArgs])
  have e2 := hm (.x2,.slot fSig) (by simp [verifyArgs])
  have e3 := hm (.x3,.slot fScr) (by simp [verifyArgs])
  rw [hc.slotV (f := fKey) (j := 0) rfl (by decide)] at e0
  rw [hc.off] at e1
  rw [hc.slotV (f := fSig) (j := 6) rfl (by decide)] at e2
  rw [hc.slotV (f := fScr) (j := 7) rfl (by decide)] at e3
  simp only [Message.Lay.vals,List.getD_cons_zero,List.getD_cons_succ] at e0 e2 e3
  exact ⟨e0,e1,e2,e3⟩

def messageVerifyCallRd (p : Params) (prepared : Bool) (s : State) : List Region :=
  [⟨s.gpr .x0,rawVerifyBytes p prepared⟩,⟨(messageVerifyLay p prepared s).MU,64⟩,⟨s.gpr .x5,p.sigLen⟩]

def messageVerifyCallWr (p : Params) (s : State) : List Region := [⟨s.gpr .x6,sScr p⟩]

theorem message_verify_call_base_pre {p : Params} (hp : Ok3 p) {prepared : Bool} {s t u : State}
    {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (h : MessageVerifyFacts p prepared s)
    (cache : prepared = true → PreparedPublicKey p s.mem (s.gpr .x0))
    (h8 : (s.gpr .x4).toNat < 256)
    (hc : Ctx (messageVerifyLay p prepared s) g v s.mem t)
    (hm : (∀ da ∈ verifyArgs,u.gpr da.1 = da.2.val t) ∧
      VG.Proof.MlKem.AArch64.Only (verifyArgs.map (·.1)) t u) :
    (rawVerifyK p prepared abi).pre
      (u.callEntry.withRegions (messageVerifyCallRd p prepared s) (messageVerifyCallWr p s)) := by
  have hL := message_verify_layout_ok hp h h8
  obtain ⟨e0,e1,e2,e3⟩ := message_verify_regs hc hm.1
  have scr := sScrV_sub p s
  have mu := (mu_withinV p s).sub
  have nscr : (s.gpr .x6).toNat + sScr p ≤ 2 ^ 64 := by
    have nS := h.nScr
    simp only [mScrLen,sScr,messageScratchWords] at nS ⊢
    omega
  have sp : 64 ≤ u.sp.toNat := by rw [hm.2.sp,hc.sp]; exact h.stack
  have cache' : prepared = true → PreparedPublicKey p u.mem (s.gpr .x0) := by
    intro flag
    rw [hm.2.mem]
    apply prepared_public_frame (cache flag) hc.frame ?_ ?_
    · subst prepared
      intro R hR
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
      rcases hR with rfl | rfl
      · exact hL.xKey.symm
      · exact hL.kKey.symm
    · rcases hp with rfl | rfl | rfl <;> decide
  have hstk {R : Region} (hd : (below s.sp 64).Disjoint R) : (below u.sp 64).Disjoint R := by
    rw [hm.2.sp,hc.sp]; exact hd
  cases prepared
  all_goals
    simp only [rawVerifyK,Bool.false_eq_true,↓reduceIte]
    sig_pre [verifyContract,verifySig,preparedVerifyContract,preparedVerifySig,abi,VG.AArch64.argRegs]
    simp only [e0,e1,e2,e3,messageVerifyCallRd,messageVerifyCallWr]
    refine ⟨sp,rfl,rfl,h.keyScr.sub_right scr,mu_sScrV (ok3_params hp) s,h.sigScr.sub_right scr,
      hstk h.stkKey,hstk (h.stkScr.sub_right mu),hstk h.stkSig,hstk (h.stkScr.sub_right scr),
      h.nKey,mu_nowrap hL,h.nSig,?_⟩
    first | exact nscr | exact ⟨nscr,cache' rfl⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Spec.Sha3 (bytesAt)

def messageVerifyRootRd (v : Proof.Sha3.AArch64.Permutation) (s : State) : List Region :=
  if v.callee.pairedSha3 then verifyRootRd s else []

theorem message_verify_resources (v : Proof.Sha3.AArch64.Permutation) {p : Params} {prepared : Bool} {s : State}
    (pre : (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s) :
    (messageVerifyK p prepared abi).pre (s.withRegions (messageVerifyRd p prepared s) s.wr) ∧
    (v.callee.pairedSha3 = true → StaticRoots 64 s) ∧
    s.rd = messageVerifyRd p prepared s ++ messageVerifyRootRd v s := by
  by_cases hv : v.callee.pairedSha3 = true
  · simp only [Verify.OptimizedSelected.selectedAbi,Verify.OptimizedSelected.selectedConsts,hv,↓reduceIte] at pre
    simp only [messageVerifyRootRd,hv,↓reduceIte]
    cases prepared
    all_goals
      simp only [messageVerifyK,Bool.false_eq_true,↓reduceIte] at pre ⊢
      sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
        abi,VG.AArch64.argRegs,Abi.withConsts,signRootConsts_eq,Abi.constRegions,Abi.constsHeld,
        TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow] at pre
      obtain ⟨sp,hd,hf,hi,hff,hfw,hfs,hif,hiw,his,hfa,hia,ht,wr,
        d1,d2,d3,d4,d5,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,n6,tail⟩ := pre
      have rd := (List.take_append_drop (s.rd.length-2) s.rd).symm
      rw [ht,hd] at rd
      refine ⟨?_,fun _ => ⟨⟨hf,hff,?_,hfw,hfs,hfa⟩,⟨hi,hif,?_,hiw,his,hia⟩⟩,rd⟩
      · sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
          abi,VG.AArch64.argRegs]
        exact ⟨sp,rfl,wr,d1,d2,d3,d4,d5,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,n6,tail⟩
      · exact Covers.one ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,
          List.mem_append_left _ (by rw [rd];simp),Region.contains_self _ _⟩
      · exact Covers.one ⟨⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,
          List.mem_append_left _ (by rw [rd];simp),Region.contains_self _ _⟩
  · have hf : v.callee.pairedSha3 = false := Bool.eq_false_iff.mpr hv
    have ha : Verify.OptimizedSelected.selectedAbi v = abi := by
      simp only [Verify.OptimizedSelected.selectedAbi,Verify.OptimizedSelected.selectedConsts,hf,
        Bool.false_eq_true,↓reduceIte];rfl
    rw [ha] at pre
    refine ⟨?_,fun ht => False.elim (hv ht),?_⟩
    · cases prepared
      all_goals
        simp only [messageVerifyK,Bool.false_eq_true,↓reduceIte] at pre ⊢
        sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
          abi,VG.AArch64.argRegs] at pre ⊢
        exact ⟨pre.1,rfl,pre.2.2⟩
    · cases prepared
      all_goals
        simp only [messageVerifyK,Bool.false_eq_true,↓reduceIte] at pre
        sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
          abi,VG.AArch64.argRegs] at pre
        simpa only [messageVerifyRootRd,hf,Bool.false_eq_true,↓reduceIte,List.append_nil,messageVerifyRd,rawVerifyBytes] using pre.2.1

theorem message_verify_all_facts (v : Proof.Sha3.AArch64.Permutation) {p : Params} {prepared : Bool} {s : State}
    (pre : (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s) :
    MessageVerifyFacts p prepared s := by
  have r := message_verify_resources v pre
  have h := message_verify_facts r.1
  exact { h with reads := fun R hR => by rw [r.2.2];exact List.mem_append_left _ hR }

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Spec.Sha3 (bytesAt)

theorem message_verify_write_cover {p : Params} {prepared : Bool} {s t u : State}
    {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m : Mem}
    (h : MessageVerifyFacts p prepared s)
    (hc : Ctx (messageVerifyLay p prepared s) g v m t)
    (o : VG.Proof.MlKem.AArch64.Only (verifyArgs.map (·.1)) t u) :
    Covers (messageVerifyCallWr p s) u.wr := by
  rw [o.wr,hc.wr]
  change Covers (messageVerifyCallWr p s) s.wr
  refine covers_of_within fun R hR => ?_
  simp only [messageVerifyCallWr,List.mem_cons,List.not_mem_nil,or_false] at hR
  subst hR
  refine ⟨⟨s.gpr .x6,mScrLen p⟩,by rw [h.wr];simp,within_base _ ?_⟩
  rw [mScr_eq];simp only [sScr,oE];omega

theorem message_verify_call_pre (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {prepared : Bool} {s t u : State} {g : Reg → BitVec 64} {vv : VReg → BitVec 128}
    (pre : (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s)
    (h8 : (s.gpr .x4).toNat < 256)
    (hc : Ctx (messageVerifyLay p prepared s) g vv s.mem t)
    (hm : (∀ da ∈ verifyArgs,u.gpr da.1 = da.2.val t) ∧
      VG.Proof.MlKem.AArch64.Only (verifyArgs.map (·.1)) t u)
    (hy : u.syms = t.syms) (hr : v.callee.pairedSha3 = true → StaticRoots 64 t) :
    (rawVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre
      (u.callEntry.withRegions (messageVerifyCallRd p prepared s ++ messageVerifyRootRd v u) (messageVerifyCallWr p s)) := by
  have resources := message_verify_resources v pre
  have facts := message_verify_all_facts v pre
  have cache : prepared = true → PreparedPublicKey p s.mem (s.gpr .x0) := by
    intro flag
    subst prepared
    simpa only [State.withRegions_mem,State.withRegions_gpr] using message_verify_cache resources.1
  have base := message_verify_call_base_pre hp facts cache h8 hc hm
  by_cases hv : v.callee.pairedSha3 = true
  · have ha : Verify.OptimizedSelected.selectedAbi v = abi.withConsts signRootConsts := by
      simp only [Verify.OptimizedSelected.selectedAbi,Verify.OptimizedSelected.selectedConsts,hv,↓reduceIte]
    rw [ha]
    simp only [messageVerifyRootRd,hv,↓reduceIte]
    have pass {nm : String} {ws : List (BitVec 64)} (h : StaticTable 64 nm ws t) : StaticTable 64 nm ws u := by
      apply staticTable_reframe h (W := []) ?_ (by simp) hm.2.rd hm.2.wr hy ?_
      · rw [hm.2.mem];exact Frame.refl _ _
      · rw [hm.2.sp];exact fun _ h => h
    have root : StaticRoots 64 u := ⟨pass (hr hv).forward,pass (hr hv).inverse⟩
    have cw := message_verify_write_cover facts hc hm.2
    let rd := messageVerifyCallRd p prepared s ++ verifyRootRd u
    let wr := messageVerifyCallWr p s
    have rb : StaticRoots 64 (u.callEntry.withRegions rd wr) :=
      ⟨operation_table_reborrow root.forward (by simp [rd,verifyRootRd]) cw,
        operation_table_reborrow root.inverse (by simp [rd,verifyRootRd]) cw⟩
    obtain ⟨e0,e1,e2,_⟩ := message_verify_regs hc hm.1
    have er : rawVerifyRd p prepared (u.callEntry.withRegions rd wr) = messageVerifyCallRd p prepared s := by
      simp only [rawVerifyRd,gpr_ce u (r := .x0),gpr_ce u (r := .x1),gpr_ce u (r := .x2),e0,e1,e2]
      rfl
    apply raw_verify_pre_extend ?_ rb ?_
    · rw [er,State.withRegions_wr,State.withRegions_withRegions];exact base
    · rw [er];rfl
  · have hf : v.callee.pairedSha3 = false := Bool.eq_false_iff.mpr hv
    have ha : Verify.OptimizedSelected.selectedAbi v = abi := by
      simp only [Verify.OptimizedSelected.selectedAbi,Verify.OptimizedSelected.selectedConsts,hf,Bool.false_eq_true,↓reduceIte];rfl
    simpa only [ha,messageVerifyRootRd,hf,Bool.false_eq_true,↓reduceIte,List.append_nil] using base

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Spec.Sha3 (bytesAt)

structure MessageVerifyFn (v : Proof.Sha3.AArch64.Permutation) (p : Params) (prepared : Bool) (code : Prog isa) : Prop where
  ver : Verified target code (rawVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v))
  dle : Message.DLe 4 code

theorem message_verify_read_cover {p : Params} {prepared : Bool} {s t u : State}
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m : Mem}
    (h : MessageVerifyFacts p prepared s)
    (hc : Ctx (messageVerifyLay p prepared s) g vv m t)
    (o : VG.Proof.MlKem.AArch64.Only (verifyArgs.map (·.1)) t u) :
    Covers (messageVerifyCallRd p prepared s) (u.rd ++ u.wr) := by
  rw [o.rd,o.wr,hc.rd,hc.wr]
  change Covers (messageVerifyCallRd p prepared s) (s.rd ++ s.wr)
  refine covers_of_within fun R hR => ?_
  simp only [messageVerifyCallRd,List.mem_cons,List.not_mem_nil,or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact ⟨_,List.mem_append_left _ (h.reads _ (by simp [messageVerifyRd])),within_self _⟩
  · exact ⟨⟨s.gpr .x6,mScrLen p⟩,List.mem_append_right _ (by rw [h.wr];simp),mu_withinV p s⟩
  · exact ⟨_,List.mem_append_left _ (h.reads _ (by simp [messageVerifyRd])),within_self _⟩

theorem message_verify_call_ok (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {prepared : Bool} {s t : State} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {n : String} {code : Prog isa}
    (hV : MessageVerifyFn v p prepared code)
    (pre : (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s)
    (h8 : (s.gpr .x4).toNat < 256) (hc : Ctx (messageVerifyLay p prepared s) g vv s.mem t)
    (hr : v.callee.pairedSha3 = true → StaticRoots 64 t) :
    WP isa (callA n code verifyArgs) t fun u => Fin (messageVerifyLay p prepared s) g vv u ∧
      (let w := fun b => verifyMu p b (bytesAt t.mem (s.gpr .x0) p.pkLen)
          (bytesAt t.mem (messageVerifyLay p prepared s).MU 64) (bytesAt t.mem (s.gpr .x5) p.sigLen);
        ((u.gpr .x0).setWidth 32 = 1 ∧ ∃ b,w b = some true) ∨
          ((u.gpr .x0).setWidth 32 = 0 ∧ w minBounds ≠ some true)) := by
  have h := message_verify_all_facts v pre
  have hL := message_verify_layout_ok hp h h8
  refine WP.seq (WP.mono_syms (setArgs_ok verifyArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA,o⟩ hsy => ?_)
  have c1 : Ctx (messageVerifyLay p prepared s) g vv s.mem t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs (fun r hr' _ => o.gpr r (by
      simp only [verifyArgs,List.map_cons,List.map_nil];exact not_pres hr' _))
  obtain ⟨e0,e1,e2,_⟩ := message_verify_regs hc hA
  have hpre := message_verify_call_pre v hp pre h8 hc ⟨hA,o⟩ hsy hr
  have cw := message_verify_write_cover h hc o
  have hd := hV.dle.le
  refine WP.callFV hV.ver.1 hpre ?_ cw (fun u rdu wru spu fu csu vsu post => ?_) (by omega)
  · apply Covers.append_left (Covers.append_left (message_verify_read_cover h hc o) ?_) cw.right
    by_cases hv : v.callee.pairedSha3 = true
    · simp only [messageVerifyRootRd,hv,↓reduceIte,verifyRootRd,hsy,o.rd,o.wr]
      exact Covers.pair (hr hv).forward.readable (hr hv).inverse.readable
    · simp only [messageVerifyRootRd,Bool.eq_false_iff.mpr hv,Bool.false_eq_true,↓reduceIte]
      exact Covers.nil
  · have saved : ∀ d,d+8≤88 → u.mem.readW ((messageVerifyLay p prepared s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
        t1.mem.readW ((messageVerifyLay p prepared s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 := by
      intro d hD
      apply fu.readW (Region.contains_self _ _) ?_ (by decide)
      intro R hR
      simp only [messageVerifyCallWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hR
      rcases hR with rfl | rfl
      · exact sv_sScrV (ok3_params hp) s hD
      · rw [c1.sp,Offset.add_add]
        exact (h.stkScr.symm.sub_left ((within_off (messageVerifyLay p prepared s).X
          (d := 904+d) (n := 8) (k := 1024) (by omega)).trans (messageVerifyLay_X p prepared s)).sub).sub_right
          (below_sub (by omega) (by decide))
    refine ⟨⟨rdu.trans c1.rd,wru.trans c1.wr,spu.trans c1.sp,
      (csu .x28 (by decide) (by decide)).trans c1.x28,
      (fun r hr' h28 h30 => (csu r hr' h30).trans (c1.cs r hr' h28 h30)),
      (fun r hr' => (vsu r hr').trans (c1.vs r hr')),
      (saved 0 (by decide)).trans c1.s28,(saved 8 (by decide)).trans c1.s30⟩,?_⟩
    cases hmode : v.callee.pairedSha3 <;> cases prepared
    all_goals
      simp only [rawVerifyK,Bool.false_eq_true,↓reduceIte,Verify.OptimizedSelected.selectedAbi,
        Verify.OptimizedSelected.selectedConsts,hmode] at post
      sig_post [verifyContract,verifySig,preparedVerifyContract,preparedVerifySig,
        abi,VG.AArch64.argRegs,Verify.OptimizedSelected.selectedAbi,Abi.withConsts] at post
      simpa only [e0,e1,e2,o.mem,messageVerifyLay,Optimized.CachedVerify.cachedLay] using post

theorem message_verify_roots_ctx (v : Proof.Sha3.AArch64.Permutation) {p : Params} {prepared : Bool} {s t : State}
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128}
    (pre : (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s)
    (hc : Ctx (messageVerifyLay p prepared s) g vv s.mem t) (hy : t.syms = s.syms)
    (hv : v.callee.pairedSha3 = true) : StaticRoots 64 t := by
  have resources := message_verify_resources v pre
  have h := message_verify_all_facts v pre
  have xs := (messageVerifyLay_X p prepared s).sub
  have stackSub : Region.Sub (below t.sp 64) (below s.sp 64) := by rw [hc.sp];exact fun _ h => h
  have pass {nm : String} {ws : List (BitVec 64)} (ht : StaticTable 64 nm ws s) : StaticTable 64 nm ws t := by
    apply staticTable_reframe ht hc.frame ?_ hc.rd hc.wr hy stackSub
    intro R hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with rfl | rfl
    · exact (ht.writable _ (by rw [h.wr];simp)).sub_right xs
    · exact ht.stack.sub_right (below_sub (by decide) (by decide))
  exact ⟨pass (resources.2.1 hv).forward,pass (resources.2.1 hv).inverse⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

theorem message_verify_saves {p : Params} {prepared : Bool} {s s1 : State}
    (o : VG.Proof.MlKem.AArch64.Only [.x9] s s1) :
    ∀ j (hj : j < cachedVerifySaves.length),s1.gpr (cachedVerifySaves[j]'hj).1 =
      (messageVerifyLay p prepared s).vals.getD j 0 :=
  CachedVerify.cachedSaves_vals (p := p) o

theorem message_verify_correct (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {prepared : Bool} {n : String} {code : Prog isa} (hV : MessageVerifyFn v p prepared code)
    {s : State} (pre : (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s) :
    WP isa (verifyMessageCached v.callee n code p) s fun u =>
      abiPreserved s u ∧ (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).post s u := by
  have h := message_verify_all_facts v pre
  unfold verifyMessageCached top
  refine WP.seq (WP.mono_syms (lsr_ok s) fun s1 ⟨o1,hc1⟩ hy1 => ?_)
  by_cases h8 : (s.gpr .x4).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := message_verify_layout_ok hp h h8
    refine wp_ite_f hc1 (WP.seq (WP.mono_syms
      (enter_ok hL rfl (by decide) rfl (o1.get .x6) (by rw [o1.sp];rfl)
        (by rw [o1.rd];rfl) (by rw [o1.wr];rfl) (o1.get .x4)
        (message_verify_saves (p := p) (prepared := prepared) o1) (by decide)) fun t hc hyt => ?_))
    have hXtr : (messageVerifyLay p prepared s).XS.Disjoint ⟨s.gpr .x7,64⟩ :=
      h.trScr.symm.sub_left (messageVerifyLay_X p prepared s).sub
    have htr : bytesAt t.mem (s.gpr .x7) 64 = pkTr (bytesAt s.mem (s.gpr .x0) p.pkLen) := by
      rw [hc.bytesAt_eq hXtr (h.stkTr.sub_left (below_sub (by decide) (by decide))) (by decide),o1.mem]
      exact h.digest
    refine WP.seq (WP.seq (WP.mono_syms (muHash_ok v hL hc (tr := .slot fRnd) (by decide) rfl
      (fun t' hc' => by rw [hc'.slotV (f := fRnd) (j := 5) rfl (by decide)];rfl)
      ⟨⟨s.gpr .x7,64⟩,List.mem_append_left _ (h.reads _ (by simp [messageVerifyRd])),within_self _⟩
      (hXtr.symm.sub_right (Region.sub_prefix (by decide)))
      (hXtr.symm.sub_right (within_off (messageVerifyLay p prepared s).X (d := 200) (n := 640) (k := 1024) (by decide)).sub)
      (h.stkTr.sub_left (below_sub (by decide) (by decide)))) fun t2 ⟨hc2,hmu⟩ hymu => ?_))
    have ctx : Ctx (messageVerifyLay p prepared s) s1.gpr s1.v s.mem t2 := by simpa only [o1.mem] using hc2
    have roots := message_verify_roots_ctx v pre ctx (hymu.trans (hyt.trans hy1))
    refine WP.mono (message_verify_call_ok v hp hV pre h8 ctx roots) fun u ⟨hf,hq⟩ => ?_
    refine WP.mono (leave_ok hL hf) fun z ⟨cs,sp,vs,mem,x0,_,_⟩ => ?_
    refine ⟨⟨(fun r hr => by rw [cs r hr];exact o1.get r (by
      simp only [List.mem_singleton];intro e;subst r;revert hr;decide)),sp,
      (fun r hr => (vs r hr).trans (o1.vcs r hr))⟩,?_⟩
    have kp : Region.Sub ⟨s.gpr .x0,p.pkLen⟩ (messageVerifyLay p prepared s).KEY :=
      Region.sub_prefix (by change p.pkLen ≤ rawVerifyBytes p prepared;cases prepared <;> simp [rawVerifyBytes,preparedPublicKeyBytes])
    have ek : bytesAt t2.mem (s.gpr .x0) p.pkLen = bytesAt s.mem (s.gpr .x0) p.pkLen :=
      ctx.bytesAt_eq (hL.xKey.sub_right kp) (hL.kKey.sub_right kp) (by rcases hp with rfl | rfl | rfl <;> decide)
    have es : bytesAt t2.mem (s.gpr .x5) p.sigLen = bytesAt s.mem (s.gpr .x5) p.sigLen :=
      ctx.bytesAt_eq (h.sigScr.symm.sub_left (messageVerifyLay_X p prepared s).sub)
        (h.stkSig.sub_left (below_sub (by decide) (by decide))) (by have := h.nSig;omega)
    rw [ek,es,hmu,htr,o1.mem] at hq
    cases hmode : v.callee.pairedSha3 <;> cases prepared
    all_goals
      simp only [messageVerifyK,Bool.false_eq_true,↓reduceIte,Verify.OptimizedSelected.selectedAbi,
        Verify.OptimizedSelected.selectedConsts,hmode]
      sig_post [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
        abi,VG.AArch64.argRegs,Verify.OptimizedSelected.selectedAbi,Verify.OptimizedSelected.selectedConsts,hmode,Abi.withConsts]
      rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length];exact h8),x0]
      simpa only [verifyInternal,messageRep,pkTr,hdrBytes,Proof.MlKem.bytesAt_length,
        messageVerifyLay,CachedVerify.cachedLay,List.append_assoc] using hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine wp_ite_t hc1 (VG.Proof.MlKem.AArch64.wp_movz fun s2 o2 e2 => VG.Proof.MlKem.AArch64.wp_nil
      ⟨⟨(fun r hr => ?_),by rw [o2.sp,o1.sp],(fun r hr => by rw [o2.vcs r hr,o1.vcs r hr])⟩,?_⟩)
    · have h0 : r ∉ [Reg.x0] := fun e => by simp only [List.mem_singleton] at e;subst r;revert hr;decide
      have h9 : r ∉ [Reg.x9] := fun e => by simp only [List.mem_singleton] at e;subst r;revert hr;decide
      rw [o2.get r h0,o1.get r h9]
    · cases hmode : v.callee.pairedSha3 <;> cases prepared
      all_goals
        simp only [messageVerifyK,Bool.false_eq_true,↓reduceIte,Verify.OptimizedSelected.selectedAbi,
          Verify.OptimizedSelected.selectedConsts,hmode]
        sig_post [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
          abi,VG.AArch64.argRegs,Verify.OptimizedSelected.selectedAbi,Verify.OptimizedSelected.selectedConsts,hmode,Abi.withConsts]
        rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length];omega),e2]
        rfl

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

def messageVerifyRootsAt (v : Proof.Sha3.AArch64.Permutation) (s : State) : Addr × Addr :=
  if v.callee.pairedSha3 then Message.Optimized.rootsAt s else (0,0)

def messageVerifyPairRegions (v : Proof.Sha3.AArch64.Permutation) (tab : Addr × Addr) : List Region :=
  if v.callee.pairedSha3 then Message.Optimized.rootPairRegions tab else []

theorem messageVerifyRootsAt_syms (v : Proof.Sha3.AArch64.Permutation) {s t : State} (hy : s.syms = t.syms) :
    messageVerifyRootsAt v s = messageVerifyRootsAt v t := by
  unfold messageVerifyRootsAt
  rw [Message.Optimized.rootsAt_syms hy]

theorem messageVerifyRootRd_eq (v : Proof.Sha3.AArch64.Permutation) (s : State) :
    messageVerifyRootRd v s = messageVerifyPairRegions v (messageVerifyRootsAt v s) := by
  cases hv : v.callee.pairedSha3 <;> simp only [messageVerifyRootRd,messageVerifyPairRegions,messageVerifyRootsAt,
    hv,Bool.false_eq_true,↓reduceIte]; rfl

def MessageVerifyOK (v : Proof.Sha3.AArch64.Permutation) (p : Params) (prepared : Bool)
    (L : Message.Lay) (m : Mem) (t : State) : Prop :=
  ∃ s,(messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s ∧
    (s.gpr .x4).toNat < 256 ∧ messageVerifyLay p prepared s = L ∧ s.mem = m ∧ t.syms = s.syms

theorem message_verify_call_tr (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {prepared : Bool} {n : String} {code : Prog isa} (hV : MessageVerifyFn v p prepared code) (tab : Addr × Addr) :
    RelCT isa (Two (verifyI p) (fun L m t => MessageVerifyOK v p prepared L m t ∧
      CachedVerify.VMuOk p L m t ∧ messageVerifyRootsAt v t = tab))
      (callA n code verifyArgs) (fun _ _ => True) := by
  refine Message.Optimized.call_tr (by decide) hV.ver.1 hV.ver.2.1
    (fun L => [⟨L.key,rawVerifyBytes p prepared⟩,⟨L.MU,64⟩,⟨L.sig,p.sigLen⟩] ++ messageVerifyPairRegions v tab)
    (fun L => [⟨L.scr,sScr p⟩])
    (fun L g vv m t u hL hc phi hm => ?_)
    (fun L g1 g2 v1 v2 m1 m2 a b a1 b1 hL hi c1 c2 ph1 ph2 f1 f2 => ?_)
    (fun L g vv m t hL hc phi => ?_)
  · obtain ⟨⟨s,pre,h8,rfl,em,hy⟩,_,htab⟩ := phi
    have ctx : Ctx (messageVerifyLay p prepared s) g vv s.mem t := by rw [em];exact hc
    have roots := message_verify_roots_ctx v pre ctx hy
    have hpre := message_verify_call_pre v hp pre h8 ctx hm.1 hm.2 roots
    have er : messageVerifyRootRd v u = messageVerifyPairRegions v tab := by
      rw [messageVerifyRootRd_eq,messageVerifyRootsAt_syms v hm.2,htab]
    simpa only [er,messageVerifyCallRd,messageVerifyCallWr,messageVerifyLay,CachedVerify.cachedLay] using hpre
  · obtain ⟨s,pre,h8,rfl,_,_⟩ := ph1.1
    have facts := message_verify_all_facts v pre
    obtain ⟨x0,x1,x2,x3⟩ := message_verify_regs c1 f1.1.1
    obtain ⟨y0,y1,y2,y3⟩ := message_verify_regs c2 f2.1.1
    have kp : Region.Sub (⟨s.gpr .x0,p.pkLen⟩ : Region) (messageVerifyLay p prepared s).KEY :=
      Region.sub_prefix (by change p.pkLen ≤ rawVerifyBytes p prepared;cases prepared <;> simp [rawVerifyBytes,preparedPublicKeyBytes])
    have ek : ∀ {g vv m a u},Ctx (messageVerifyLay p prepared s) g vv m a → Moved verifyArgs a u →
        bytesAt u.mem (s.gpr .x0) p.pkLen = bytesAt m (s.gpr .x0) p.pkLen := by
      intro g vv m a u c f
      rw [f.2.mem]
      exact c.bytesAt_eq (hL.xKey.sub_right kp) (hL.kKey.sub_right kp)
        (by rcases hp with rfl | rfl | rfl <;> decide)
    have es : ∀ {g vv m a u},Ctx (messageVerifyLay p prepared s) g vv m a → Moved verifyArgs a u →
        bytesAt u.mem (s.gpr .x5) p.sigLen = bytesAt m (s.gpr .x5) p.sigLen := by
      intro g vv m a u c f
      rw [f.2.mem]
      exact c.bytesAt_eq (facts.sigScr.symm.sub_left (messageVerifyLay_X p prepared s).sub)
        (facts.stkSig.sub_left (below_sub (by decide) (by decide))) (by have := facts.nSig;omega)
    have emu : ∀ {a u},Moved verifyArgs a u → bytesAt u.mem (messageVerifyLay p prepared s).MU 64 =
        bytesAt a.mem (messageVerifyLay p prepared s).MU 64 := by intro a u f;rw [f.2.mem]
    have keys : ∀ q,(messageVerifyLay p q s).key = s.gpr .x0 := fun _ => rfl
    have sigs : ∀ q,(messageVerifyLay p q s).sig = s.gpr .x5 := fun _ => rfl
    have leak : leakBytes (bytesAt a1.mem (s.gpr .x0) p.pkLen ++ bytesAt a1.mem (messageVerifyLay p prepared s).MU 64 ++ bytesAt a1.mem (s.gpr .x5) p.sigLen) =
        leakBytes (bytesAt b1.mem (s.gpr .x0) p.pkLen ++ bytesAt b1.mem (messageVerifyLay p prepared s).MU 64 ++ bytesAt b1.mem (s.gpr .x5) p.sigLen) := by
      rw [ek c1 f1.1,ek c2 f2.1,es c1 f1.1,es c2 f2.1,emu f1.1,emu f2.1,ph1.2.1,ph2.2.1]
      obtain ⟨ik,im,ic,is⟩ := verifyI_eq hi
      have ik' : bytesAt m1 (s.gpr .x0) p.pkLen = bytesAt m2 (s.gpr .x0) p.pkLen := ik
      have is' : bytesAt m1 (s.gpr .x5) p.sigLen = bytesAt m2 (s.gpr .x5) p.sigLen := is
      rw [ik,im,ic,ik',is']
    have sp : a1.sp = b1.sp := by rw [f1.1.2.sp,f2.1.2.sp,c1.sp,c2.sp]
    have tabs := (messageVerifyRootsAt_syms v f1.2).trans
      (ph1.2.2.trans ((messageVerifyRootsAt_syms v f2.2).trans ph2.2.2).symm)
    cases hmode : v.callee.pairedSha3 <;> cases prepared
    all_goals
      simp only [rawVerifyK,Bool.false_eq_true,↓reduceIte,Verify.OptimizedSelected.selectedAbi,
        Verify.OptimizedSelected.selectedConsts,hmode]
      sig_pub [verifyContract,verifySig,preparedVerifyContract,preparedVerifySig,abi,VG.AArch64.argRegs,
        Abi.withConsts,signRootConsts_eq]
      simp only [x0,x1,x2,x3,y0,y1,y2,y3,keys,sigs,and_true]
      first
      | exact ⟨sp,leak⟩
      | have tf := congrArg Prod.fst tabs
        have ti := congrArg Prod.snd tabs
        simp only [messageVerifyRootsAt,hmode,↓reduceIte,Message.Optimized.rootsAt] at tf ti
        exact ⟨sp,tf,ti,leak⟩
  · obtain ⟨⟨s,pre,h8,rfl,em,hy⟩,_,htab⟩ := phi
    have ctx : Ctx (messageVerifyLay p prepared s) g vv s.mem t := by rw [em];exact hc
    have roots := message_verify_roots_ctx v pre ctx hy
    have identity := VG.Proof.MlKem.AArch64.Only.refl (verifyArgs.map (·.1)) t
    have reads := message_verify_read_cover (message_verify_all_facts v pre) hc identity
    have writes := message_verify_write_cover (message_verify_all_facts v pre) hc identity
    have rt : messageVerifyRootRd v t = messageVerifyPairRegions v tab := by rw [messageVerifyRootRd_eq,htab]
    have rcov : Covers (messageVerifyPairRegions v tab) (t.rd ++ t.wr) := by
      rw [← rt]
      by_cases hv : v.callee.pairedSha3 = true
      · simp only [messageVerifyRootRd,hv,↓reduceIte,verifyRootRd]
        exact Covers.append_left (roots hv).forward.readable (roots hv).inverse.readable
      · simp only [messageVerifyRootRd,Bool.eq_false_iff.mpr hv,Bool.false_eq_true,↓reduceIte]
        exact Covers.nil
    rw [hc.rd,hc.wr] at reads rcov
    rw [hc.wr] at writes
    exact ⟨Covers.append_left (Covers.append_left reads rcov) writes.right,writes⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

theorem message_verify_tr_side (v : Proof.Sha3.AArch64.Permutation) {p : Params} {prepared : Bool}
    {L : Message.Lay} {m : Mem} {t : State} (h : MessageVerifyOK v p prepared L m t) :
    RootedCachedVerify.TrSide L := by
  obtain ⟨s,pre,_,rfl,_,_⟩ := h
  have facts := message_verify_all_facts v pre
  exact ⟨⟨⟨s.gpr .x7,64⟩,List.mem_append_left _ (facts.reads _ (by simp [messageVerifyRd])),within_self _⟩,
    facts.trScr.symm.sub_left (messageVerifyLay_X p prepared s).sub,
    facts.stkTr.sub_left (below_sub (by decide) (by decide))⟩

theorem message_verify_digest (v : Proof.Sha3.AArch64.Permutation) {p : Params} {prepared : Bool}
    {L : Message.Lay} {g vv m} {t : State} (h : MessageVerifyOK v p prepared L m t)
    (hc : Ctx L g vv m t) : bytesAt t.mem L.rnd 64 = H (bytesAt m L.key p.pkLen) 64 := by
  rw [hc.bytesAt_eq (message_verify_tr_side v h).x (message_verify_tr_side v h).stack (by decide)]
  obtain ⟨s,pre,_,rfl,rfl,_⟩ := h
  exact (message_verify_all_facts v pre).digest

theorem message_verify_body_tr (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {prepared : Bool} (tab : Addr × Addr) {n : String} {code : Prog isa} (hV : MessageVerifyFn v p prepared code) :
    RelCT isa (Two (verifyI p) (fun L m t => MessageVerifyOK v p prepared L m t ∧ messageVerifyRootsAt v t = tab))
      (.seq (muHash v.callee (.slot fRnd)) (callA n code verifyArgs))
      (fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp) := by
  let Phi := fun L m t => MessageVerifyOK v p prepared L m t ∧ messageVerifyRootsAt v t = tab
  let Psi := fun L m t => MessageVerifyOK v p prepared L m t ∧ CachedVerify.VMuOk p L m t ∧ messageVerifyRootsAt v t = tab
  have hash := muHash_tr_of v (I := verifyI p) (Φ := Phi) (G := RootedCachedVerify.TrSide)
    (tr := .slot fRnd) (by decide) rfl (fun L => L.rnd)
    (fun L g vv m t c => RootedCachedVerify.cachedTr_val c) (fun _ _ h => h.parts)
  have hash' : RelCT isa (Two (verifyI p) Phi) (muHash v.callee (.slot fRnd)) (fun _ _ => True) :=
    RelCT.mono hash (fun _ _ h => by
      obtain ⟨L,g1,g2,v1,v2,m1,m2,hL,hi,c1,c2,ph1,ph2⟩ := h
      exact ⟨L,g1,g2,v1,v2,m1,m2,hL,hi,c1,c2,
        ⟨message_verify_tr_side v ph1.1,ph1⟩,⟨message_verify_tr_side v ph2.1,ph2⟩⟩) (fun _ _ _ => trivial)
  have hashed := two_wp (I := verifyI p) (Φ := Phi) (Ψ := Psi) hash'
    (fun L g vv m t hL c phi => by
      obtain ⟨a,b,c',d⟩ := (message_verify_tr_side v phi.1).parts
      refine WP.mono_syms (muHash_ok v hL c (tr := .slot fRnd) (by decide) rfl
        (fun t' hc => RootedCachedVerify.cachedTr_val hc) a b c' d) (fun t' ⟨ct,mu⟩ hy => ?_)
      obtain ⟨⟨s,pre,h8,eL,em,hs⟩,htab⟩ := phi
      refine ⟨ct,⟨s,pre,h8,eL,em,hy.trans hs⟩,?_,(messageVerifyRootsAt_syms v hy).trans htab⟩
      unfold CachedVerify.VMuOk
      rw [mu,message_verify_digest v ⟨s,pre,h8,eL,em,hs⟩ c])
  have run : ∀ {L : Message.Lay} {g vv m t},L.Ok → Ctx L g vv m t → Phi L m t →
      WP isa (.seq (muHash v.callee (.slot fRnd)) (callA n code verifyArgs)) t
        (fun u => u.gpr .x28 = t.gpr .x28 ∧ u.sp = t.sp) := by
    intro L g vv m t hL c phi
    obtain ⟨a,b,c',d⟩ := (message_verify_tr_side v phi.1).parts
    obtain ⟨⟨s,pre,h8,rfl,em,hy⟩,_⟩ := phi
    refine WP.seq (WP.mono_syms (muHash_ok v hL c (tr := .slot fRnd) (by decide) rfl
      (fun t' hc => RootedCachedVerify.cachedTr_val hc) a b c' d) (fun t' ⟨ct,_⟩ hsy => ?_))
    have ctx : Ctx (messageVerifyLay p prepared s) g vv s.mem t' := by rw [em];exact ct
    have roots := message_verify_roots_ctx v pre ctx (hsy.trans hy)
    exact WP.mono (message_verify_call_ok v hp hV pre h8 ctx roots) (fun u h =>
      ⟨h.1.x28.trans c.x28.symm,h.1.sp.trans c.sp.symm⟩)
  refine RelCT.postDep (F := fun t u => u.gpr .x28 = t.gpr .x28 ∧ u.sp = t.sp)
    (hashed.seq (message_verify_call_tr v hp hV tab)) ?_ ?_
  · rintro x y ⟨L,g1,g2,v1,v2,m1,m2,hL,_,c1,c2,ph1,ph2⟩
    exact ⟨run hL c1 ph1,run hL c2 ph2⟩
  · rintro x y x' y' ⟨L,g1,g2,v1,v2,m1,m2,_,_,c1,c2,_,_⟩ fx fy
    exact ⟨by rw [fx.1,fy.1,c1.x28,c2.x28],by rw [fx.2,fy.2,c1.sp,c2.sp]⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized

structure MessageVerifyPub (v : Proof.Sha3.AArch64.Permutation) (p : Params) (s t : State)
    extends CachedVerify.VPub p s t where
  roots : messageVerifyRootsAt v s = messageVerifyRootsAt v t

theorem message_verify_pub (v : Proof.Sha3.AArch64.Permutation) {p : Params} {prepared : Bool} {s t : State}
    (h : (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pub s t) :
    MessageVerifyPub v p s t := by
  cases hmode : v.callee.pairedSha3 <;> cases prepared
  all_goals
    simp only [messageVerifyK,Bool.false_eq_true,↓reduceIte,Verify.OptimizedSelected.selectedAbi,
      Verify.OptimizedSelected.selectedConsts,hmode] at h
    sig_pub [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
      abi,VG.AArch64.argRegs,Abi.withConsts,signRootConsts_eq] at h
    first
    | obtain ⟨sp,leak,x0,x1,x2,x3,x4,x5,x6,x7⟩ := h
      exact ⟨⟨sp,leak,x0,x1,x2,x3,x4,x5,x6,x7⟩,by simp only [messageVerifyRootsAt,hmode,Bool.false_eq_true,↓reduceIte]⟩
    | obtain ⟨sp,hf,hi,leak,x0,x1,x2,x3,x4,x5,x6,x7⟩ := h
      refine ⟨⟨sp,leak,x0,x1,x2,x3,x4,x5,x6,x7⟩,?_⟩
      simp only [messageVerifyRootsAt,hmode,↓reduceIte,Message.Optimized.rootsAt]
      exact Prod.ext hf hi

theorem message_verify_layout_eq (v : Proof.Sha3.AArch64.Permutation) {p : Params} {prepared : Bool} {s t : State}
    (hs : (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s)
    (ht : (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre t)
    (pub : MessageVerifyPub v p s t) : messageVerifyLay p prepared s = messageVerifyLay p prepared t := by
  have fs := message_verify_all_facts v hs
  have ft := message_verify_all_facts v ht
  have rd : s.rd = t.rd := by
    rw [(message_verify_resources v hs).2.2,(message_verify_resources v ht).2.2]
    simp only [messageVerifyRd,pub.x0,pub.x1,pub.x2,pub.x3,pub.x4,pub.x5,pub.x7,
      messageVerifyRootRd_eq,pub.roots]
  have wr : s.wr = t.wr := by rw [fs.wr,ft.wr,pub.x6]
  simp only [messageVerifyLay,CachedVerify.cachedLay,pub.sp,pub.x0,pub.x1,pub.x2,pub.x3,
    pub.x4,pub.x5,pub.x6,pub.x7,rd,wr]

abbrev MessageVerifyRel (v : Proof.Sha3.AArch64.Permutation) (p : Params) (prepared : Bool) (x y : State) : Prop :=
  (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre x ∧
  (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre y ∧
  (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pub x y

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
variable {p : Params} {prepared : Bool}

theorem message_verify_ct (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hS : MessageVerifyFn v p prepared c)
    (hp : Ok3 p) :
    ConstantTime isa (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pub
      (verifyMessageCached v.callee n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s₁ ∧
      (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s₂ ∧ (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pub s₁ s₂) =
      Ghost (MessageVerifyRel v p prepared) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessageCached top
  -- `x9 ← ctx_len >> 8`.
  have hlsr := ghost_step (P := MessageVerifyRel v p prepared) (A := fun x a => a = x) (B := fun x a => ALsr x a ∧ a.syms=x.syms) (c := .block [.lsr .x .x9 .x4 8])
    (AArch64.taintRel [] (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨(message_verify_pub v hxy.2.2).sp, by simp⟩) lsr_taint)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩), WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩)⟩
  refine RelCT.seq hlsr (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.1.2, f₂.1.2, (message_verify_pub v hxy.2.2).x4]) ?_ ?_)
  · -- `ctx_len ≥ 256`: return 2.
    exact AArch64.taintRel [] (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ =>
      ⟨by rw [f₁.1.1.sp, f₂.1.1.sp]; exact (message_verify_pub v hxy.2.2).sp, by simp⟩) movz2_taint
  · -- The entry.
    let A : State → State → Prop := fun x a => (ALsr x a ∧ a.syms=x.syms) ∧ isa.eval (.nonzero .x .x9) a = some false
    let B : State → State → Prop := fun x t => (x.gpr .x4).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (messageVerifyLay p prepared x) a.gpr a.v a.mem t ∧ t.syms=x.syms
    have hent := ghost_step (P := MessageVerifyRel v p prepared) (A := A) (B := B) (c := .block (enter .x6 p cachedVerifySaves))
      (AArch64.taintRel [.x6] (fun a b ⟨x, y, hxy, f₁, f₂⟩ => ⟨by rw [f₁.1.1.1.sp, f₂.1.1.1.sp]; exact (message_verify_pub v hxy.2.2).sp,
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [f₁.1.1.1.get .x6, f₂.1.1.1.get .x6]; exact (message_verify_pub v hxy.2.2).x6⟩) (RootedCachedVerify.enterV_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre x' → A x' a' →
            WP isa (.block (enter .x6 p cachedVerifySaves)) a' (B x') := fun x' a' hx ⟨⟨⟨o, e⟩, hy⟩, ef⟩ => by
          have h8 : (x'.gpr .x4).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have hL := message_verify_layout_ok hp (message_verify_all_facts v hx) h8
          exact WP.mono_syms (enter_ok hL rfl (by decide) rfl (o.get .x6) (by rw [o.sp]; rfl) (by rw [o.rd]; rfl)
            (by rw [o.wr]; rfl) (o.get .x4) (message_verify_saves (p := p) (prepared := prepared) o) (by decide)) fun t hc hyt => ⟨h8, a', o.mem, hc, hyt.trans hy⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.1.2, ← (message_verify_pub v hxy.2.2).x4, ← f₁.1.2]; exact hc⟩⟩) fun _ _ h => h) (RelCT.seq (RelCT.mono (RelCT.exists_ fun tab => message_verify_body_tr v hp tab hS) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca, sya⟩,
      ⟨h8y, b', mb, cb, syb⟩⟩ => ?_) fun _ _ h => h) (AArch64.taintRel [.x28] (fun a b h => ⟨h.2, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1⟩) leave_taint))
    have hx := message_verify_all_facts v hxy.1
    have hy := message_verify_all_facts v hxy.2.1
    have hpub := message_verify_pub v hxy.2.2
    have e := message_verify_layout_eq v hxy.1 hxy.2.1 hpub
    refine ⟨messageVerifyRootsAt v x,messageVerifyLay p prepared x,a'.gpr,b'.gpr,a'.v,b'.v,a'.mem,b'.mem,
      message_verify_layout_ok hp hx h8x,?_,ca,e ▸ cb,
      ⟨⟨x,hxy.1,h8x,rfl,ma.symm,sya⟩,messageVerifyRootsAt_syms v sya⟩,
      ⟨⟨y,hxy.2.1,h8y,e.symm,mb.symm,syb⟩,(messageVerifyRootsAt_syms v syb).trans hpub.roots.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.x0, ← hpub.x1, ← hpub.x2, ← hpub.x3, ← hpub.x4, ← hpub.x5] at lk
    unfold verifyI
    rw [ma, mb]
    exact lk

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

def messageVerifySat (v : Proof.Sha3.AArch64.Permutation) (p : Params) (prepared : Bool) (m : Mem) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x80000 | .x2 => 0 | .x3 => 0x90000
    | .x4 => 0 | .x5 => 0x30000 | .x6 => 0x400000 | .x7 => 0x8000 | _ => 0
  sp := 0x1000000
  mem := m
  syms name := if name = "VG_MLDSA_NTT_EXPANDED" then 1048576 else 1052480
  rd := [⟨0x10000,rawVerifyBytes p prepared⟩,⟨0x80000,0⟩,⟨0x90000,0⟩,⟨0x30000,p.sigLen⟩,⟨0x8000,64⟩] ++
    (if v.callee.pairedSha3 then [⟨1048576,3904⟩,⟨1052480,3904⟩] else [])
  wr := [⟨0x400000,mScrLen p⟩]

theorem message_verify_pre_extend (v : Proof.Sha3.AArch64.Permutation) {p : Params} {prepared : Bool} {s : State}
    (h : (messageVerifyK p prepared abi).pre (s.withRegions (messageVerifyRd p prepared s) s.wr))
    (hr : v.callee.pairedSha3 = true → StaticRoots 64 s)
    (hd : s.rd = messageVerifyRd p prepared s ++ messageVerifyRootRd v s) :
    (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s := by
  cases hmode : v.callee.pairedSha3 <;> cases prepared
  all_goals
    simp only [messageVerifyK,Bool.false_eq_true,↓reduceIte,Verify.OptimizedSelected.selectedAbi,
      Verify.OptimizedSelected.selectedConsts,hmode,show abi.withConsts [] = abi by rfl] at h ⊢
    sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
      abi,VG.AArch64.argRegs] at h
    sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
      abi,VG.AArch64.argRegs,Abi.withConsts,signRootConsts_eq,Abi.constRegions,Abi.constsHeld,
      TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow]
    obtain ⟨sp,_,wr,d1,d2,d3,d4,d5,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,n6,tail⟩ := h
    first
    | have rd := hd
      simp only [messageVerifyRootRd,hmode,Bool.false_eq_true,↓reduceIte,List.append_nil] at rd
      exact ⟨sp,rd,wr,d1,d2,d3,d4,d5,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,n6,tail⟩
    | have roots := hr hmode
      have rd := hd
      simp only [messageVerifyRootRd,hmode,↓reduceIte] at rd
      exact ⟨sp,by rw [rd];rfl,roots.forward.held,roots.inverse.held,roots.forward.fit,
        roots.forward.writable,roots.forward.stack,roots.inverse.fit,roots.inverse.writable,roots.inverse.stack,
        roots.forward.aligned,roots.inverse.aligned,by rw [rd];rfl,
        wr,d1,d2,d3,d4,d5,k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,n6,tail⟩

theorem messageVerifySat_bare (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) (prepared : Bool) (m : Mem)
    (cache : PreparedPublicKey p m 0x10000)
    (digest : bytesAt m 0x8000 64 = pkTr (bytesAt m 0x10000 p.pkLen)) :
    (messageVerifyK p prepared abi).pre
      ((messageVerifySat v p prepared m).withRegions
        (messageVerifyRd p prepared (messageVerifySat v p prepared m)) (messageVerifySat v p prepared m).wr) := by
  cases prepared
  all_goals
    rcases hp with rfl | rfl | rfl
    all_goals
      simp only [messageVerifyK,Bool.false_eq_true,↓reduceIte]
      sig_pre [verifyMessageCachedContract,verifyMessageCachedSig,preparedVerifyMessageContract,preparedVerifyMessageSig,
        abi,VG.AArch64.argRegs]
      simp only [messageVerifyRd,messageVerifySat,rawVerifyBytes,Bool.false_eq_true,↓reduceIte]
      sig_and_intros
      all_goals first | exact cache | exact digest | exact Region.disjoint_of_sep (by decide) | decide +kernel

theorem messageVerifySat_roots (v : Proof.Sha3.AArch64.Permutation) (p : Params) (hp : Ok3 p) (prepared : Bool) (m : Mem)
    (hf : ∀ i < 488,m.readW (1048576 + BitVec.ofNat 64 (8*i)) 64 = Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0)
    (hi : ∀ i < 488,m.readW (1052480 + BitVec.ofNat 64 (8*i)) 64 = Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (hmode : v.callee.pairedSha3 = true) : StaticRoots 64 (messageVerifySat v p prepared m) := by
  have forward : StaticTable 64 "VG_MLDSA_NTT_EXPANDED" Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords
      (messageVerifySat v p prepared m) := by
    refine ⟨hf,by dsimp [messageVerifySat];decide,?_,?_,
      by apply Region.disjoint_of_sep;dsimp [messageVerifySat];decide,
      by dsimp [messageVerifySat]⟩
    · exact Covers.one ⟨⟨1048576,3904⟩,by simp [messageVerifySat,hmode],Region.contains_self _ _⟩
    · intro R hR
      simp only [messageVerifySat,List.mem_cons,List.not_mem_nil,or_false] at hR
      subst R
      simp only [messageVerifySat]
      rcases hp with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  have inverse : StaticTable 64 "VG_MLDSA_INV_FOLDED" Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords
      (messageVerifySat v p prepared m) := by
    refine ⟨hi,by dsimp [messageVerifySat];decide,?_,?_,
      by apply Region.disjoint_of_sep;dsimp [messageVerifySat];decide,
      by dsimp [messageVerifySat]⟩
    · exact Covers.one ⟨⟨1052480,3904⟩,by simp [messageVerifySat,hmode],Region.contains_self _ _⟩
    · intro R hR
      simp only [messageVerifySat,List.mem_cons,List.not_mem_nil,or_false] at hR
      subst R
      simp only [messageVerifySat]
      rcases hp with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  exact ⟨forward,inverse⟩

theorem messageVerifySat_pre (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) (prepared : Bool) (m : Mem)
    (hf : ∀ i < 488,m.readW (1048576 + BitVec.ofNat 64 (8*i)) 64 = Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords.getD i 0)
    (hi : ∀ i < 488,m.readW (1052480 + BitVec.ofNat 64 (8*i)) 64 = Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (cache : PreparedPublicKey p m 0x10000)
    (digest : bytesAt m 0x8000 64 = pkTr (bytesAt m 0x10000 p.pkLen)) :
    (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre (messageVerifySat v p prepared m) := by
  apply message_verify_pre_extend v (messageVerifySat_bare v hp prepared m cache digest)
    (messageVerifySat_roots v p hp prepared m hf hi)
  rfl

theorem public_preparation_preserves_digest {p : Params} (hp : Ok3 p) {m : Mem} {t : State} {tr : List Leak}
    (he : Exec isa (Impl.MlDsa.AArch64.PreparedKey.preparePublic p) (prepWithTables p m) tr t) :
    bytesAt t.mem 0x8000 64 = bytesAt m 0x8000 64 := by
  have hd := prepare_public_depth hp
  have frame := Exec.frameSp he (by omega : 16 * (Impl.MlDsa.AArch64.PreparedKey.preparePublic p).aarch64Depth < 2^64)
  apply Proof.MlKem.bytesAt_frame frame ?_ (by decide)
  intro R hR
  simp only [prepWithTables,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hR
  rcases hR with rfl | rfl | rfl
  all_goals
    rcases hp with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem message_verify_sat (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) (prepared : Bool) :
    ∃ s,(messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)).pre s := by
  have src := RootedCachedVerify.cachedPre_of (RootedCachedVerify.verify_sat hp)
  let m := (RootedCachedVerify.verifySat p).mem
  obtain ⟨_,t,he,_,post⟩ := public_correct hp (prepWithTables p m) (prepWithTables_pre hp m)
  sig_post [preparePublicKeyContract,preparePublicKeySig,abi,VG.AArch64.argRegs] at post
  have keyCopy : bytesAt t.mem 0x10000 p.pkLen = bytesAt m 0x1000 p.pkLen := post.1
  have digest : bytesAt t.mem 0x8000 64 = pkTr (bytesAt t.mem 0x10000 p.pkLen) := by
    rw [public_preparation_preserves_digest hp he,keyCopy]
    exact src.digest
  have forward := public_preparation_preserves_roots hp he (base := 1048576) (.inl rfl)
  have inverse := public_preparation_preserves_roots hp he (base := 1052480) (.inr rfl)
  exact ⟨messageVerifySat v p prepared t.mem,messageVerifySat_pre v hp prepared t.mem
    (fun i hi' => (forward i hi').trans (src.roots.forward.held i hi'))
    (fun i hi' => (inverse i hi').trans (src.roots.inverse.held i hi')) post.2 digest⟩

theorem message_verify_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {prepared : Bool} {n : String} {code : Prog isa} (hV : MessageVerifyFn v p prepared code) :
    Verified target (verifyMessageCached v.callee n code p)
      (messageVerifyK p prepared (Verify.OptimizedSelected.selectedAbi v)) :=
  ⟨(fun _ h => let ⟨tr,t,he,ha,hq⟩ := message_verify_correct v hp hV h; ⟨tr,t,he,ha,hq⟩),
    message_verify_ct v hV hp,message_verify_sat v hp prepared⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.AArch64.Sign

def verifyCode (v : Proof.Sha3.AArch64.Permutation) (p : Params) (name : String)
    (prepared : Bool) : Prog isa :=
  Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
    (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache v.callee
      (VG.Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) p prepared

theorem message_verify_fn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    (name : String) (prepared : Bool) : MessageVerifyFn v p prepared (verifyCode v p name prepared) := by
  refine ⟨verify_entry_verified v hp name prepared,⟨?_⟩⟩
  have hd := (verify_withCache_dle v p).le
  simpa only [verifyCode,Impl.MlDsa.AArch64.PreparedKey.Verify.entry,
    Code.aarch64Depth,Instr.frameUnits,Nat.zero_max] using Nat.add_le_add_right hd 1

end VG.Proof.MlDsa.AArch64.PreparedKey
