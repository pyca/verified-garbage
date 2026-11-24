module
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.Flag
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Gcm.Contiguous
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousEntryCT
import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousDeferred
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
public import VerifiedGarbage.Proof.AesGcm.X86_64.Leaves
public import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous
import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.ScrubFill
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified

/-! Register one contiguous AES-GCM seal per x86-64 backend. The caller supplies identical or disjoint payload buffers. The whole-record proof covers both layouts, including the prepared-key flag, the private work area, and register cleanup. -/

@[expose] public section
namespace VG.Proof.AesGcm.SealBuffers
open VG VG.Spec.Gcm VG.Spec.Aes

abbrev Agree (m₁ m₂ : Mem) (p : Addr) (n : Nat) : Prop :=
  ∀ a, (⟨p,n⟩ : Region).Contains a 1 → m₁ a = m₂ a

/-- The full-tag encryption equation used by the operations on an expanded key. -/
def Equation (ctx nonce aad src dst tag : Addr) (rounds nl al n : Nat) (m out : Mem) : Prop :=
  encryptWith (ctxCiph m ctx rounds) (ctxH m ctx) 16 (bytesAt m nonce nl) (bytesAt m src n)
    (bytesAt m aad al) = (bytesAt out dst n,bytesAt out tag 16)

theorem keyed {ctx nonce aad src dst tag : Addr} {rounds nl al n : Nat} {m out : Mem} {key : List Byte}
    (hk : KeyRounds m ctx rounds key) (h : Equation ctx nonce aad src dst tag rounds nl al n m out) :
    aesGcmEncrypt key 16 (bytesAt m nonce nl) (bytesAt m src n) (bytesAt m aad al) =
      (bytesAt out dst n,bytesAt out tag 16) := by
  obtain ⟨cipher,hash,_⟩ := keyRounds_ctx hk
  unfold Equation at h
  rwa [cipher,hash,← encrypt_eq] at h

theorem keyRounds_local {m m' : Mem} {ctx : Addr} {rounds : Nat} {key : List Byte}
    (h : Agree m m' ctx 256) (hk : KeyRounds m ctx rounds key) : KeyRounds m' ctx rounds key := by
  obtain ⟨_,_,r⟩ := keyRounds_ctx hk
  refine ⟨hk.1,hk.2.1,?_,(ctxH_congr (agree_of h)).trans hk.2.2.2⟩
  rw [bytesAt_congr (fun i hi => agree_of h i (by rw [← hk.2.1] at hi; rcases r with r|r|r <;> omega))]; exact hk.2.2.1

theorem prepared_local {m m' : Mem} {ctx : Addr} (h : Agree m m' ctx 1032) (valid : PreparedRepr m ctx) :
    PreparedRepr m' ctx :=
  (Flag.flaggedPowers_congr (agree_of h) (show Flag.FlaggedPowers 0 m ctx from ⟨Nat.zero_le _,valid⟩)).2

end VG.Proof.AesGcm.SealBuffers

namespace VG.Proof.AesGcm.SealBuffers
open VG VG.Spec.Gcm

abbrev sig := sealContiguousSig 129

theorem agreements {m₁ m₂ : Mem} {k r iv nl ad al src dst n tag : Addr}
    (h : ∀ b ∈ Sig.bufs sig.params [k,r,iv,nl,ad,al,src,dst,n,tag], Agree m₁ m₂ b.1.base b.1.len) :
    Agree m₁ m₂ k 1032 ∧ Agree m₁ m₂ iv nl.toNat ∧ Agree m₁ m₂ ad al.toNat ∧ Agree m₁ m₂ src n.toNat ∧
      Agree m₁ m₂ dst n.toNat ∧ Agree m₁ m₂ tag 16 := by
  by_cases eq : src=dst
  · subst src
    simp [sig, sealContiguousSig, Sig.bufs, Elem.size] at h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  · simpa [sig,sealContiguousSig,Sig.bufs,Elem.size,eq] using h

theorem postInputs (vs : List Addr) (m m' out : Mem) (r : BitVec 0) (hl : vs.length=(sig.words 64).length)
    (hb : ∀ b∈Sig.bufs sig.params vs, ∀ a,b.1.Contains a 1 → m a=m' a)
    (h : Curry.apply (sig.words 64) (sealContiguousPost 64) vs m out r) :
    Curry.apply (sig.words 64) (sealContiguousPost 64) vs m' out r := by
  match vs,hl with
  | [k,rounds,iv,nl,ad,al,src,dst,n,tag],_ =>
    obtain ⟨key,nonce,aad,pt,_⟩ := agreements hb
    intro sk hk
    have hₖ := keyRounds_local (m:=m') (m':=m) (fun a ha => (key a ((Region.sub_prefix (show 256≤1032 by decide)) _ ha)).symm) hk
    change Spec.Gcm.aesGcmEncrypt sk 16 (Spec.Aes.bytesAt m' iv nl.toNat) (Spec.Aes.bytesAt m' src n.toNat) (Spec.Aes.bytesAt m' ad al.toNat) = _
    rw [bytesAt_congr (agree_of nonce),bytesAt_congr (agree_of pt),bytesAt_congr (agree_of aad)]
    exact h sk hₖ

theorem postOutputs (vs : List Addr) (m out out' : Mem) (r : BitVec 0) (hl : vs.length=(sig.words 64).length)
    (hb : ∀ b∈Sig.bufs sig.params vs, ∀ a,b.1.Contains a 1 → out a=out' a)
    (h : Curry.apply (sig.words 64) (sealContiguousPost 64) vs m out r) :
    Curry.apply (sig.words 64) (sealContiguousPost 64) vs m out' r := by
  match vs,hl with
  | [k,rounds,iv,nl,ad,al,src,dst,n,tag],_ =>
    obtain ⟨_,_,_,_,d,t⟩ := agreements hb
    intro sk hk
    change _ = (Spec.Aes.bytesAt out' dst n.toNat,Spec.Aes.bytesAt out' tag 16)
    rw [bytesAt_congr (agree_of d),bytesAt_congr (agree_of t)]
    exact h sk hk

end VG.Proof.AesGcm.SealBuffers

namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.Scrub
open VG.Impl.AesGcm.X86_64 (Fn Callees)
open VG.Impl.AesGcm.X86_64.Contiguous

abbrev allowance := fun (_ : String) => 8

private theorem fillBody {k : Nat} {c : Callees} (hs : CalleesSide k c)
    {sk ker : Prog isa} (fk : Fill k allowance sk ker) (vec wide prep : Bool) :
    Fill k allowance (core (body stub5 vec wide prep sk)) (core (body c vec wide prep ker)) := by
  obtain ⟨hc,_,hg,_,_⟩ := hs
  cases vec <;> cases wide <;> cases prep <;>
    repeat (any_goals (first
      | exact Fill.refl _
      | exact fk
      | refine Fill.seq ?_ ?_
      | exact Fill.hole _ _ (by assumption)
      | refine Fill.ite _ ?_ ?_
      | refine Fill.loop _ ?_
      | refine Fill.call _ _ ?_
      | refine Fill.frame _ _ ?_))

private theorem fillDeferred {k : Nat} {c : Callees} {ctr : Fn} (hs : CalleesSide k c)
    (ht : calleeSide ctr.code k 8=true) :
    Fill k allowance (core (deferredBody stub5 ctrToStub)) (core (deferredBody c ctr)) := by
  obtain ⟨hc,_,hg,_,_⟩ := hs
  fill_calls_wide

private theorem fillSeparate {k : Nat} {ctr gh : Fn} (ct : calleeSide ctr.code k 8=true)
    (hg : calleeSide gh.code k 8=true) :
    Fill k allowance (separate ctrToStub stub5.gh) (separate ctr gh) := by fill_calls_wide

private theorem fillFused {k : Nat} {f : Fn} (hf : calleeSide f.code k 8 = true) :
    Fill k allowance (fused (fnStub "B")) (fused f) := by fill_calls_wide

private theorem frameFill {k : Nat} {r s : Prog isa} (f : Fill k allowance (core r) (core s)) :
    Fill k allowance (framed r) (framed s) := .frame _ _ (.seq (.block _) f)

theorem selectedFill {k : Nat} {c : Callees} {ctr : Fn} {blocks : Option Fn}
    (defer wide : Bool) (n : Nat) (hs : CalleesSide k c) (ct : calleeSide ctr.code k 8=true)
    (hb : ∀ f∈blocks, calleeSide f.code k 8=true) :
    Fill k allowance (selected defer wide n stub5 ctrToStub (blocks.map fun _ => fnStub "B"))
      (selected defer wide n c ctr blocks) := by
  cases blocks with
  | none =>
    cases defer
    · exact frameFill (fillBody hs (fillSeparate ct hs.gh) false wide false)
    · exact frameFill (fillDeferred hs ct)
  | some f =>
    have ready := frameFill (fillBody hs (fillFused (hb f rfl)) true wide true)
    refine .seq (.block _) (.ite _ (.seq (.seq (.block _) (.block _)) ready) ?_)
    cases defer
    · exact frameFill (fillBody hs (fillSeparate ct hs.gh) true wide false)
    · exact frameFill (fillDeferred hs ct)

theorem plainSide (defer : Bool) :
    stubSide (selected defer false 16 stub5 ctrToStub none) 0 allowance 2640 []=true := by
  cases defer <;> lit_decide

theorem vectorSide (wide : Bool) :
    stubSide (selected false wide (if wide then 48 else 16) stub5 ctrToStub (some (fnStub "B")))
      (if wide then 2 else 1) allowance 2640 []=true := by
  cases wide <;> lit_decide

abbrev Sp (c : Prog isa) := c.all (fun i => !isa.writesSp i)=true

private theorem spParts (v : GcmImpl) :
    Sp (Impl.AesGcm.X86_64.oneAad v.callees) ∧ Sp (Impl.AesGcm.X86_64.cryptTailG v.callees true) ∧
    Sp (Impl.AesGcm.X86_64.oneTag v.callees 0) := by
  have a := seal_spSafe v
  simp only [Impl.AesGcm.X86_64.«seal»,Code.all,Bool.and_eq_true] at a
  obtain ⟨_,aa,_,_,⟨tg,_⟩,_⟩ := a
  refine ⟨aa,?_,tg⟩
  simp only [Sp,Impl.AesGcm.X86_64.cryptTailG,Code.all,GcmImpl.callees,v.ctr.spSafe]
  decide +kernel

private theorem spBody (v : GcmImpl) {p : Prog isa} (hp : Sp p) (vec wide prep : Bool) :
    Sp (core (body v.callees vec wide prep p)) := by
  obtain ⟨aa,tail,tg⟩ := spParts v
  unfold Sp at *
  cases vec <;> cases wide <;> cases prep <;>
    simp only [core,body,aad,bulk,finishScalar,Code.all,hp,aa,tail,tg,Bool.true_and,Bool.and_true,ite_true,ite_false,
      Bool.false_eq_true,Bool.false_and] <;> decide +kernel

private theorem spDeferred (v : GcmImpl) {ctr : Fn} (ct : Sp ctr.code) :
    Sp (core (deferredBody v.callees ctr)) := by
  obtain ⟨aa,tail,tg⟩ := spParts v
  unfold Sp at *
  simp only [Impl.AesGcm.X86_64.oneTag,Code.all,Bool.and_eq_true] at tg
  simp only [core,deferredBody,bulk,Impl.AesGcm.X86_64.Contiguous.call,Code.all,ct,aa,tail,tg.2,Bool.true_and,Bool.and_true]
  decide +kernel

/-- Properties needed before assigning a private work area to the raw entry. -/
structure CoreSafe (record : Prog isa) : Prop where
  sp : Sp (core record)
  depth : (core record).x86_64Depth ≤ 24
  mx : (core record).allInstrs (fun i => !loadsMxcsr i)=true

private theorem rawSafe {r : Prog isa} {k : Nat} (sp : Sp (core r)) (h : calleeSide (core r) k 24=true) :
    CoreSafe r := by
  simp only [calleeSide,Bool.and_eq_true,decide_eq_true_eq] at h
  refine ⟨sp,h.1.1,?_⟩
  have both := (Code.allInstrs_eq _ _).symm.trans h.1.2
  exact (Code.allInstrs_eq _ _).trans (List.all_eq_true.mpr fun i hi =>
    (Bool.and_eq_true_iff.mp (List.all_eq_true.mp both i hi)).2)

private theorem separateCoreSide (vec wide : Bool) :
    stubCallee (core (body stub5 vec wide false (separate ctrToStub stub5.gh)))
      (if vec then (if wide then 2 else 1) else 0) allowance 24=true := by
  cases vec <;> cases wide <;> lit_decide

private theorem fusedCoreSide (wide : Bool) :
    stubCallee (core (body stub5 true wide true (fused (fnStub "B"))))
      (if wide then 2 else 1) allowance 24=true := by cases wide <;> lit_decide

private theorem delayedCoreSide :
    stubCallee (core (deferredBody stub5 ctrToStub)) 0 allowance 24=true := by lit_decide

private theorem separateSp (v : GcmImpl) {ctr : Fn} (ct : Sp ctr.code) : Sp (separate ctr v.callees.gh) := by
  simp only [Sp,separate,Impl.AesGcm.X86_64.Contiguous.call,Code.all,GcmImpl.callees,v.gh.spSafe,ct,Bool.true_and,Bool.and_true]
  decide +kernel

private theorem fusedSp {f : Fn} (h : Sp f.code) : Sp (fused f) := by
  simp only [Sp,fused,Impl.AesGcm.X86_64.Contiguous.call,Code.all,h,Bool.and_true]
  decide +kernel

theorem separateSafe (v : GcmImpl) (vec wide : Bool) {ctr : Fn} {k : Nat} (hs : CalleesSide k v.callees)
    (hc : calleeSide ctr.code k 8=true) (sp : Sp ctr.code) (hk : (if vec then (if wide then 2 else 1) else 0)≤k) :
    CoreSafe (body v.callees vec wide false (separate ctr v.callees.gh)) :=
  rawSafe (spBody v (separateSp v sp) vec wide false)
    (calleeSide_of_fill (fillBody hs (fillSeparate hc hs.gh) vec wide false) hk (separateCoreSide vec wide))

theorem fusedSafe (v : GcmImpl) (wide : Bool) {f : Fn} {k : Nat} (hs : CalleesSide k v.callees)
    (hf : calleeSide f.code k 8=true) (sp : Sp f.code) (hk : (if wide then 2 else 1)≤k) :
    CoreSafe (body v.callees true wide true (fused f)) :=
  rawSafe (spBody v (fusedSp sp) true wide true)
    (calleeSide_of_fill (fillBody hs (fillFused hf) true wide true) hk (fusedCoreSide wide))

theorem delayedSafe (v : GcmImpl) {ctr : Fn} {k : Nat} (hs : CalleesSide k v.callees)
    (hc : calleeSide ctr.code k 8=true) (sp : Sp ctr.code) : CoreSafe (deferredBody v.callees ctr) :=
  rawSafe (spDeferred v sp) (calleeSide_of_fill (fillDeferred hs hc) (Nat.zero_le _) delayedCoreSide)

theorem selectedSp (v : GcmImpl) {ctr : Fn} (defer wide : Bool) (n : Nat) {b : Option Fn}
    (ct : Sp ctr.code) (hb : ∀ f∈b, Sp f.code) : Sp (selected defer wide n v.callees ctr b) := by
  have base (vec : Bool) : Sp (if defer then framed (deferredBody v.callees ctr) else one v.callees vec wide false (separate ctr v.callees.gh)) := by
    cases defer
    · exact withStackArgScratch_spSafe (spBody v (separateSp v ct) vec wide false)
    · exact withStackArgScratch_spSafe (spDeferred v ct)
  cases b with
  | none => exact base false
  | some f =>
    exact onFlag_spSafe (withStackArgScratch_spSafe (spBody v (fusedSp (hb f rfl)) true wide true)) (base true)

open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open DirectGather (ctrFn)

/-- One functional, leakage and stack certificate for an AES-GCM record body. -/
structure RecordProof (M : CtxMode) (p : Prog isa) : Prop where
  ok : RecordOk M p
  ct : RecordCT M p
  safe : CoreSafe p

theorem plainProof (v : GcmVariant) (defer vec wide : Bool) {k : Nat} (backend : v.lvTW.level≤k)
    (level : (if vec then (if wide then 2 else 1) else 0)≤k) {M : CtxMode} :
    RecordProof M (if defer then deferredBody v.impl.callees (ctrFn v) else
      body v.impl.callees vec wide false (separate (ctrFn v) v.impl.callees.gh)) := by
  have side : calleeSide (ctrFn v).code k 8=true :=
    calleeSide_mono (Nat.le_trans (level_join_right _ _) backend) (Nat.zero_le _) v.ctrTo.side
  cases defer
  · have bulk : BulkOk M (Impl.AesGcm.X86_64.Contiguous.bulk (separate (ctrFn v) v.impl.callees.gh)) :=
      fun h o a b c => separate_bulk_ok v.ctrTo v.impl.gh h o a b c
    exact ⟨plain_ok Short.shortFacts v.impl vec wide _ bulk,plain_ct Short.shortFacts v.impl vec wide bulk
      (separate_ct v.ctrTo v.impl.gh) (separate_keeps v.ctrTo v.impl.gh),
      separateSafe v.impl vec wide ((callees_sideTW v).mono backend) side v.ctrTo.spSafe level⟩
  · exact ⟨deferred_ok v.impl v.ctrTo,deferred_ct v.impl v.ctrTo,
      delayedSafe v.impl ((callees_sideTW v).mono backend) side v.ctrTo.spSafe⟩

private theorem preparedProof {np : Nat} {hn : 8≤np ∧ np≤24} (v : GcmVariant) (wide : Bool)
    (leaf : BlocksTo.SealFn (CtxMode.preparedN np hn))
    (pow : wide → Short.PowOk (CtxMode.preparedN np hn) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP)
    (side : calleeSide leaf.fn.code v.lvT.level 8=true) (level : (if wide then 2 else 1)≤v.lvT.level) :
    RecordProof (CtxMode.preparedN np hn) (body v.impl.callees true wide true (fused leaf.fn)) := by
  have bulk : BulkOk _ (Impl.AesGcm.X86_64.Contiguous.bulk (fused leaf.fn)) := fun h o a b c => fused_bulk_ok leaf h o a b c
  exact ⟨prepared_ok Short.shortFacts v.impl wide pow _ bulk,prepared_ct Short.shortFacts v.impl wide pow
    (fun _ => Short.powersP_ct) bulk (fused_ct leaf) (fused_keeps leaf),fusedSafe v.impl wide (callees_sideT v)
    side leaf.spAll level⟩

theorem ready16Proof (v : GcmVariant) {leaf} (selected : leaf∈sealLeafR16 v) (level : 1≤v.lvT.level) :
    RecordProof CtxMode.prepared16 (body v.impl.callees true false true (fused leaf.fn)) :=
  preparedProof v false leaf (fun h => Bool.noConfusion h) (calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _)
    (selectSealLeaf_side v _ _ _ _ _ selected)) level

theorem ready48Proof (v : GcmVariant) {leaf} (selected : leaf∈sealLeafR v) (level : 2≤v.lvT.level) :
    RecordProof CtxMode.prepared (body v.impl.callees true true true (fused leaf.fn)) :=
  preparedProof v true leaf (fun _ => Short.powOk_powersP) (calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _)
    (selectSealLeaf_side v _ _ _ _ _ selected)) level

end VG.Proof.AesGcm.X86_64.ContiguousSeal

namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm

abbrev Condition := Addr → Addr → Mem → Prop
def workSig : Sig := {sealContiguousSig 129 with params := (sealContiguousSig 129).params ++ [("scratch",.array true .u64 320)]}
def pre (P : Condition) : Curry ((sealContiguousSig 129).words 64) (Mem → Prop) := fun k r _ _ _ _ _ _ _ _ => P k r
def workContract (P : Condition) : Contract isa :=
  workSig.contract abi (pre:=fun k r _ _ _ _ _ _ _ _ _ => P k r)
    (post:=fun k r np nl a al src dst len tag _ => sealContiguousPost 64 k r np nl a al src dst len tag)
    (writeArgs:=true) (stack:=32)

theorem entryPublic {P : Condition} {s t : State} (h : (workContract P).pub s t) : EntryPublic s t := by
  have arg (i : Nat) := h.2.1 i
  refine ⟨?_,?_⟩
  · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    exacts [arg 0 (by decide),arg 1 (by decide),arg 2 (by decide),arg 3 (by decide),
      arg 4 (by decide),arg 5 (by decide),h.1.1]
  · intro i hi
    have idx : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases idx with rfl|rfl|rfl|rfl|rfl
    exacts [arg 6 (by decide),arg 7 (by decide),arg 8 (by decide),arg 9 (by decide),arg 10 (by decide)]

theorem entryPost {P : Condition} {s t : State} (h : EntryPost s t) : (workContract P).post s t := by
  sig_post [workContract,workSig,sealContiguousSig,sealContiguousPost,abi,argRegs,Gather.stackArgs_five,List.append_eq]
  intro key hk
  exact SealBuffers.keyed hk h

theorem entryPre {P : Condition} {M : CtxMode} {s : State}
    (valid : P (K s) (s.gpr .rsi) s.mem → rounds s ∧ M.ok s.mem (K s))
    (h : (workContract P).pre s) : EntryPre M s := by
  have b : Region.Sub (below (SP s) 24) (below (SP s) 32) := below_sub (by decide) (by decide)
  by_cases same : stackArg s 0=stackArg s 1
  all_goals
    sig_pre [workContract,workSig,sealContiguousSig,abi,argRegs,Gather.stackArgs_five,List.cons_append,List.nil_append] at h
    simp only [same,↓reduceIte] at h
    simp [Sig.pairFacts,Sig.conj,List.filterMap_cons,and_assoc] at h
  case pos =>
    obtain ⟨room,top,rd,wr,kd,_,kw,nd,_,nw,ad,_,aw,dt,dw,da,tw,_,wa,_,_,_,rett,rt,rw,_,sk,sn,sa,sd,_,sw,_,bk,bn,ba,bd,_,bw,p⟩ := h
    have sameAddr : S s=D s := same
    have L : Proof.AesGcm.oneLay M.len 4 5 s 1 2 :=
      ⟨kd.sub_left (Region.sub_prefix M.le),kw.sub_left (Region.sub_prefix M.le),nd,nw,ad,aw,dw,da,wa,rett,rw,
       (sk.sub_left b).sub_right (Region.sub_prefix M.le),sn.sub_left b,sa.sub_left b,sd.sub_left b,sw.sub_left b,by omega_using [M.le,bk],bn,ba,bd,by change (stackArg s 4).toNat+2560≤2^64; omega_using [bw],by omega_arith,by omega_arith,(valid p).1⟩
    apply EntryPre.ofLayout L _ _ _ _ _ _ (valid p).2 _ (Or.inl sameAddr) (sameAddr ▸ dw) (sameAddr ▸ (sd.sub_left b).symm)
      (sameAddr ▸ bd) _ dt.symm tw rt
    · exact covers_prefix (k:=1032) (covers_of_mem (by simp [rd,K])) M.le
    all_goals apply covers_of_mem; simp [rd,wr,D,N,S,T,W,SP,stackArgAddr,same]
  case neg =>
    obtain ⟨room,top,rd,wr,kd,_,kw,nd,_,nw,ad,_,aw,sd,_,sw,dt,dw,da,tw,_,wa,_,_,_,_,rett,rt,rw,_,sk,sn,sa,ss,ds,_,ws,_,bk,bn,ba,bs,bd,_,bw,p⟩ := h
    have L : Proof.AesGcm.oneLay M.len 4 5 s 1 2 :=
      ⟨kd.sub_left (Region.sub_prefix M.le),kw.sub_left (Region.sub_prefix M.le),nd,nw,ad,aw,dw,da,wa,rett,rw,
       (sk.sub_left b).sub_right (Region.sub_prefix M.le),sn.sub_left b,sa.sub_left b,ds.sub_left b,ws.sub_left b,by omega_using [M.le,bk],bn,ba,bd,by change (stackArg s 4).toNat+2560≤2^64; omega_using [bw],by omega_arith,by omega_arith,(valid p).1⟩
    apply EntryPre.ofLayout L _ _ _ _ _ _ (valid p).2 _ (Or.inr sd) sw (ss.sub_left b).symm bs _ dt.symm tw rt
    · exact covers_prefix (k:=1032) (covers_of_mem (by simp [rd,K])) M.le
    all_goals apply covers_of_mem; simp [rd,wr,D,N,S,T,W,SP,stackArgAddr]

/-- A zero-length in-place record, with valid zero powers in the prepared key. -/
def witnessMem (a : Addr) : Byte :=
  if a=0x1400 then 48 else if a=0x9021 then 0x50 else if a=0x9029 then 0x60 else 0

def witness (scratch : Bool) : State :=
  { Gather.gatherSat with
    mem := witnessMem
    rd := [⟨0x1000,1032⟩,⟨0x2000,0⟩,⟨0x3000,0⟩,⟨0x9008,if scratch then 40 else 32⟩]
    wr := [⟨0,0⟩,⟨0x5000,16⟩]++(if scratch then [⟨0x6000,2560⟩] else []) }

theorem witnessPowers : Proof.AesGcm.Flag.FlaggedPowers 48 witnessMem 0x1000 := by
  apply Proof.AesGcm.Flag.flaggedPowers_of_zeroMem (Nat.le_refl _)
  · intro i hi
    have lo := Gather.ctx_low hi
    simp only [witnessMem,Proof.AesGcm.Flag.ctx_ne1024 hi,ite_false]
    have a : (0x1000+BitVec.ofNat 64 i : Addr)≠0x9021 := fun e => lo (by rw [e]; decide)
    have b : (0x1000+BitVec.ofNat 64 i : Addr)≠0x9029 := fun e => lo (by rw [e]; decide)
    simp only [a,b,ite_false]
  · decide +kernel

theorem workSat {P : Condition} (ok : P 0x1000 10 witnessMem) : (workContract P).pre (witness true) := by
  sig_pre [workContract,workSig,sealContiguousSig,abi,argRegs,Gather.stackArgs_five,List.cons_append,List.nil_append,
    witness,Gather.gatherSat,stackArg,stackArgAddr,Mem.readW,Mem.read,witnessMem]
  simp
  repeat' apply And.intro
  all_goals first | exact ok | exact Region.disjoint_of_sep (by decide)

private theorem stackFour (s : State) : List.map (stackArg s) (List.range 4) =
  [stackArg s 0,stackArg s 1,stackArg s 2,stackArg s 3] := rfl

theorem publicSat {P : Condition} (ok : P 0x1000 10 witnessMem) :
    ((sealContiguousSig 129).contract abi (pre P) (sealContiguousPost 64) true 2640).pre (witness false) := by
  sig_pre [pre,sealContiguousSig,abi,argRegs,stackFour,List.cons_append,List.nil_append,
    witness,Gather.gatherSat,stackArg,stackArgAddr,Mem.readW,Mem.read,witnessMem]
  simp
  repeat' apply And.intro
  all_goals first | exact ok | exact Region.disjoint_of_sep (by decide)

def plainP : Condition := fun _ r _ => r.toNat=10 ∨ r.toNat=12 ∨ r.toNat=14
def powerP (t : Nat) : Condition := fun k r m => plainP k r m ∧ Proof.AesGcm.Flag.FlaggedPowers t m k

abbrev PreLocal (P : Condition) :=
  ∀ {k r : Addr} {m m' : Mem}, SealBuffers.Agree m m' k 1032 → P k r m → P k r m'

theorem preLocal {P : Condition} (loc : PreLocal P) (vs : List Addr) (m m' : Mem) (hl : vs.length=(SealBuffers.sig.words 64).length)
    (hb : ∀ b∈Sig.bufs SealBuffers.sig.params vs, ∀ a,b.1.Contains a 1 → m a=m' a)
    (h : Curry.apply (SealBuffers.sig.words 64) (pre P) vs m) : Curry.apply (SealBuffers.sig.words 64) (pre P) vs m' := by
  match vs,hl with
  | [k,r,iv,nl,a,al,s,d,n,t],_ => exact loc (SealBuffers.agreements hb).1 h

theorem framedVerified {P : Condition} {M : CtxMode} {body : Prog isa} (p : RecordProof M body) (locality : PreLocal P)
    (input : ∀ {k r m}, P k r m → plainP k r m ∧ M.ok m k) (inh : P 0x1000 10 witnessMem) :
    Verified target (Impl.AesGcm.X86_64.Contiguous.framed body)
      ((sealContiguousSig 129).contract abi (pre P) (sealContiguousPost 64) true 2640) := by
  apply X86_64.Verified.stackArgScratchL (sig:=sealContiguousSig 129) (nm:="scratch") (e:=.u64) (n:=320)
    (pre:=pre P) (post:=sealContiguousPost 64) (wa:=true) (stack:=32) (bytes:=2608)
    (hpostOut:=fun vs m a b r hl _ hb _ => SealBuffers.postOutputs vs m a b r hl hb)
    _ (by decide) (by decide) (by decide) p.safe.sp (Nat.le_trans p.safe.depth (by decide))
    (fun vs a b hl hb _ => preLocal (P:=P) locality vs a b hl hb)
    (fun vs a b m r hl hb _ => SealBuffers.postInputs vs a b m r hl hb) ⟨_,publicSat inh⟩
  apply rawVerified (contract:=workContract P) p.ok p.ct p.safe.mx
    (fun _ h => entryPre input h) (fun _ _ _ => entryPost) (fun _ _ => entryPublic) ⟨_,workSat inh⟩

def preparedP : Condition := fun k r m => plainP k r m ∧ PreparedRepr m k

theorem preparedLocal : PreLocal preparedP :=
  fun h p => ⟨p.1,SealBuffers.prepared_local h p.2⟩

theorem powersLocal (t : Nat) : PreLocal (powerP t) :=
  fun h p => ⟨p.1,Proof.AesGcm.Flag.flaggedPowers_congr (agree_of h) p.2⟩

abbrev apiContract := sealContiguousPreparedApi.contract abi 2640
abbrev recordContract (P : Condition) :=
  (sealContiguousSig 129).contract abi (pre P) (sealContiguousPost 64) true 2640

theorem prepInhabited : preparedP 0x1000 10 witnessMem := ⟨Or.inl rfl,witnessPowers.2⟩
theorem powerInhabited {t : Nat} (ht : t≤48) : powerP t 0x1000 10 witnessMem :=
  ⟨Or.inl rfl,Nat.le_trans ht witnessPowers.1,witnessPowers.2⟩

theorem plainPublic {c : Prog isa} (h : Verified target c (recordContract preparedP)) :
    Verified target c apiContract :=
  Verified.leak_flag h (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)

theorem onPowers {t : Nat} (ht : t=16 ∨ t=48) {a b : Prog isa}
    (ha : Verified target a (recordContract (powerP t))) (hb : Verified target b (recordContract preparedP)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag t a b) apiContract :=
  Verified.of_onFlagCtx ht (by decide) ha hb (fun _ _ _ _ _ _ _ _ _ _ _ p hf => ⟨p.1,hf,p.2⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ p _ => p) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl) ⟨_,publicSat prepInhabited⟩

theorem outputLocal : VG.X86_64.Scrub.PostOut apiContract 0 :=
  VG.X86_64.Scrub.postOut_of_local (sig:=sealContiguousSig 129) (post:=sealContiguousPost 64)
    (leak:=some fun ctx rounds nonce nl aad al _ dst len tag => sealPreparedLeak 64 ctx rounds nonce nl aad al dst len tag)
    VG.X86_64.Scrub.ScrubAbi.plain SealBuffers.postOutputs

open VG.X86_64.Scrub
open VG.Impl.AesGcm.X86_64 (Fn Callees)
open VG.Impl.AesGcm.X86_64.Contiguous
open DirectGather (ctrFn)

abbrev Certificate (code : Prog isa) := VerifiedScrubbed target code apiContract 0 ∧ Sp code

/-- One unstitched record, sealed from either source layout. Only the
AES-NI/PCLMUL backend with legacy SSE encoding defers its GHASH call. -/
theorem unstitched (v : GcmVariant) (defer : Bool) : Certificate
    (prepared v.lvTW defer false 16 v.impl.callees (ctrFn v) none) := by
  have p := plainProof (M:=CtxMode.base) v defer false false (Nat.le_refl _) (Nat.zero_le _)
  have raw := plainPublic (framedVerified (P:=preparedP) p preparedLocal (fun h => ⟨h.1,trivial⟩) prepInhabited)
  have h : Verified target (selected defer false 16 v.impl.callees (ctrFn v) none) apiContract := by
    cases defer <;> exact raw
  have sp := selectedSp v.impl (ctr:=ctrFn v) (b:=none) defer false 16 v.ctrTo.spSafe (fun _ h => nomatch h)
  have ct : calleeSide (ctrFn v).code v.lvTW.level 8=true := calleeSide_mono (level_join_right _ _) (show 0≤8 by decide) v.ctrTo.side
  exact ⟨verifiedScrubbedAllFill (api:=sealContiguousPreparedApi)
    {suffix:="",code:=_,stack:=2640,verified:=h,spSafe:=sp} v.lvTW outputLocal
    (selectedFill (ctr:=ctrFn v) (blocks:=none) defer false 16 (callees_sideTW v) ct (fun _ mem => nomatch mem))
    (Nat.zero_le _) (Nat.le_refl _) (ha:=plainSide defer),scrubKs_spSafe sp⟩

private theorem stitched {M : CtxMode} (v : GcmVariant) (wide : Bool) (leaf : BlocksTo.SealFn M)
    (level : (if wide then 2 else 1)≤v.lvT.level)
    (side : calleeSide leaf.fn.code v.lvT.level 8=true)
    (p : RecordProof M (body v.impl.callees true wide true (fused leaf.fn)))
    (input : ∀ {k r m}, powerP (if wide then 48 else 16) k r m → plainP k r m ∧ M.ok m k) :
    Certificate (prepared v.lvT false wide (if wide then 48 else 16) v.impl.callees (ctrFn v) (some leaf.fn)) := by
  let n : Nat := if wide then 48 else 16
  have hn : n=16 ∨ n=48 := by cases wide <;> decide
  have hn' : n≤48 := by cases hn <;> omega
  have ready := framedVerified (P:=powerP n) p (powersLocal n) input (powerInhabited hn')
  have plain := framedVerified (P:=preparedP) (plainProof (M:=CtxMode.base) v false true wide v.lvTW_le_lvT level)
    preparedLocal (fun h => ⟨h.1,trivial⟩) prepInhabited
  have h := onPowers hn ready plain
  have sp := selectedSp v.impl (ctr:=ctrFn v) (b:=some leaf.fn) false wide n v.ctrTo.spSafe (by
    intro f hf; obtain rfl : leaf.fn=f := Option.mem_some_iff.mp hf; exact leaf.spAll)
  have ct : calleeSide (ctrFn v).code v.lvT.level 8=true := calleeSide_mono (Nat.le_trans (level_join_right _ _) v.lvTW_le_lvT) (show 0≤8 by decide) v.ctrTo.side
  exact ⟨verifiedScrubbedAllFill (api:=sealContiguousPreparedApi)
    {suffix:="",code:=_,stack:=2640,verified:=h,spSafe:=sp} v.lvT outputLocal
    (selectedFill (ctr:=ctrFn v) (blocks:=some leaf.fn) false wide n (callees_sideT v) ct (by
      intro f hf; obtain rfl : leaf.fn=f := Option.mem_some_iff.mp hf; exact side))
    level (Nat.le_refl _) (ha:=vectorSide wide),scrubKs_spSafe sp⟩

theorem stitched16 (v : GcmVariant) {b} (hb : b∈sealLeafR16 v) : Certificate
    (prepared v.lvT false false 16 v.impl.callees (ctrFn v) (some b.fn)) :=
  stitched v false b v.one_le_lvT (calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _)
    (selectSealLeaf_side v _ _ _ _ _ hb)) (ready16Proof v hb v.one_le_lvT)
    (fun h => ⟨h.1,h.2.2.1 h.2.1⟩)

theorem stitched48 (v : GcmVariant) {b} (hb : b∈sealLeafR v) (level : 2≤v.lvT.level) : Certificate
    (prepared v.lvT false true 48 v.impl.callees (ctrFn v) (some b.fn)) :=
  stitched v true b level (calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _)
    (selectSealLeaf_side v _ _ _ _ _ hb)) (ready48Proof v hb level)
    (fun h => ⟨h.1,h.2.2.2 h.2.1⟩)

end VG.Proof.AesGcm.X86_64.ContiguousSeal
