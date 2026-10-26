module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Local
public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Main
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
import VerifiedGarbage.Proof.Ed448.AArch64.Verify.CallsCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CT
public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Body
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Correct
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
meta import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Main
meta import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
meta import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CT
meta import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Body
meta import VerifiedGarbage.Proof.Sha3.AArch64.Variant
meta import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Correct
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed448 verification on AArch64: `Verified`

Correctness including the ABI (`verify_ok`), for any implementation `v` of
Keccak, given the sparse equation's `EqOk` from `Sparse/Verified.lean`.
Timing depends only on the public verification inputs permitted by the
reviewed contract: pointers, lengths and input bytes. Hash and scalar-reduction
correctness establish equal public challenge values in the two runs before
the sparse equation is called. Its digit branches and table addresses depend
on the public signature and challenge scalars; point coordinates are unrelated
in its timing proof. The other calls retain their content-independent timing.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Two WCtx srcValue zeroSt_ct kabs_ct kpad_ct ksqz_ct reduce_ct
  ofNat_toNat64 st_within ks_within)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame entered)

attribute [local irreducible] VG.Impl.Ed448.AArch64.Sparse.baseWords VG.Impl.X448.AArch64.Base.combWords

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

/-- The arguments of `vg_ed448_scalar_reduce`. -/
def reduceVal (L : Lay) : Reg → Addr
  | .x0 => L.E + BitVec.ofNat 64 fK
  | .x1 => L.E + BitVec.ofNat 64 fH
  | _ => L.scr

/-- The arguments of `vg_ed448_verify_equation`. -/
def equationVal (L : Lay) : Reg → Addr
  | .x0 => L.pk
  | .x1 => L.sig
  | .x2 => L.E + BitVec.ofNat 64 fK
  | _ => L.scr

/-- The positions of the sponge after each absorption. -/
abbrev q1 : Nat := (0 + 10) % 136
abbrev q2 (L : Lay) : Nat := (q1 + L.ctxLen.toNat) % 136
abbrev q3 (L : Lay) : Nat := (q2 L + 57) % 136
abbrev q4 (L : Lay) : Nat := (q3 L + 57) % 136
abbrev q5 (L : Lay) : Nat := (q4 L + L.len.toNat) % 136

theorem hash_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (Impl.Ed448.AArch64.Verify.hash v.callee)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := env_ok hL
  have hs := scrOk hL
  have z := zeroSt_ct hV hs ha₁ ha₂ (P := fun _ => True) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (by taint_decide)
  have k1 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := .val (.frame fHdr))
    (len := .val (.const 10)) (pos := .val (.const 0)) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl (by taint_decide) (P := fun _ => True)
    (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (q := 0) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (by decide) (by decide) (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
  have k2 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aCtx)
    (len := aCtxLen) (pos := .ret) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl
    (by taint_decide) (dp := L.ctx) (n := L.ctxLen.toNat) (q := q1)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 1) (by decide) _)
    (fun hm hc _ => (arg_src hL hc.1 hm (j := 2) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm)
    (fun _ _ hp => hp) (by decide) L.ctxLen.isLt (in_readable L.CTX (by simp [Lay.inputs]))
    (hL.cc.sub_right (st_within L.scr).sub) (hL.cc.sub_right (ks_within L.scr).sub) hL.cx
  have k3 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aSig)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.sig) (n := 57) (q := q2 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 5) (by decide) _) (fun _ _ _ => rfl)
    (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) (by decide)
    (.inr ⟨L.SIG, by simp [Lay.env, Lay.inputs], ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩⟩)
    ((hL.sc.sub_right (st_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    ((hL.sc.sub_right (ks_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    (hL.cs.sub_right (Region.sub_prefix (by decide)))
  have k4 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aPk)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.pk) (n := 57) (q := q3 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 0) (by decide) _) (fun _ _ _ => rfl)
    (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) (by decide) (in_readable L.PK (by simp [Lay.inputs]))
    (hL.pc.sub_right (st_within L.scr).sub) (hL.pc.sub_right (ks_within L.scr).sub) hL.cp
  have k5 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aMsg)
    (len := aLen) (pos := .ret) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl
    (by taint_decide) (dp := L.msg) (n := L.len.toNat) (q := q4 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 3) (by decide) _)
    (fun hm hc _ => (arg_src hL hc.1 hm (j := 4) (by decide) _).trans (ofNat_toNat64 L.len).symm)
    (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) L.len.isLt (in_readable L.MSG (by simp [Lay.inputs]))
    (hL.mc.sub_right (st_within L.scr).sub) (hL.mc.sub_right (ks_within L.scr).sub) hL.cm
  have p := kpad_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (pos := .ret) trivial
    (by taint_decide) (q := q5 L) (fun _ _ hp => hp) (Nat.mod_lt _ (by decide))
  have q := ksqz_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (out := .val (.frame fH))
    (show fH < 4096 by decide) rfl (by taint_decide) (P := fun _ => True) (op := L.E + BitVec.ofNat 64 fH)
    (fun _ _ _ => rfl)
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fScr, fHdr, fH]) (by simp [fScr, fHdr]) (by simp [fH])⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
  exact z.seq (k1.seq (k2.seq (k3.seq (k4.seq (k5.seq (p.seq q))))))

/-- Equal public input data produce equal signature and challenge scalars. -/
def EqInputs (L:Lay) (m n:Mem) : Prop :=
  Spec.Ed448.bytesAt m L.sig 114=Spec.Ed448.bytesAt n L.sig 114 ∧ hashIn L m=hashIn L n

def inputScalar (L:Lay) (m:Mem) : Nat:=
  Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt m L.sig 114).drop 57)

def HashReady (L:Lay) (H:List Byte) (s:State) : Prop :=
  Spec.Ed448.bytesAt s.mem (L.E+BitVec.ofNat 64 fH) 114=H

private theorem bytes_drop (m:Mem) (p:Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57=Spec.Ed448.bytesAt m (p+BitVec.ofNat 64 57) 57:=by
  refine List.ext_getElem (by simp [Spec.Ed448.bytesAt]) fun i _ _ => ?_
  simp only [Spec.Ed448.bytesAt,List.getElem_drop,List.getElem_map,List.getElem_range]
  rw [Offset.add_add]

private theorem current_scalar (hL:L.Ok) {g vec m t} (hc:WCtx L.env g vec m t) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem (L.sig+BitVec.ofNat 64 57) 57)=inputScalar L m:=by
  have hb:Spec.Ed448.bytesAt t.mem L.sig 114=Spec.Ed448.bytesAt m L.sig 114:=
    in_bytes hL hc.1 (R:=L.SIG) (by simp [Lay.inputs]) (Nat.le_refl _) (show 114≤2^64 by decide)
  rw [←bytes_drop,inputScalar,hb]

theorem body_ct (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.Sparse.EqOk)
    (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂) (heq:EqInputs L m₁ m₂) :
    RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.scr ∧
        a.syms Impl.Ed448.AArch64.Sparse.baseSym = L.T) ∧
      (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.scr ∧ b.syms Impl.Ed448.AArch64.Sparse.baseSym = L.T))
      (body v.callee) fun _ _ => True := by
  have hV := env_ok hL
  have hs := scrOk hL
  have e : RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.scr ∧
        a.syms Impl.Ed448.AArch64.Sparse.baseSym = L.T) ∧
      (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.scr ∧ b.syms Impl.Ed448.AArch64.Sparse.baseSym = L.T))
      (.block entry) (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
    VG.Proof.Ed25519.AArch64.Whole.rel_wp
      (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide))
      (fun _ h => WP.mono (entry_ok hL h.1 ha₁ h.2.1 h.2.2) fun _ hu => ⟨hu, trivial⟩)
      (fun _ h => WP.mono (entry_ok hL h.1 ha₂ h.2.1 h.2.2) fun _ hu => ⟨hu, trivial⟩)
  let S:=inputScalar L m₁
  let H:=Spec.Sha3.shake256 (hashIn L m₁) 114
  let K:=Spec.Ed448.decodeLE (Spec.Ed448.scalarReduce H)
  let M:=fun m => Args L m ∧ inputScalar L m=S
  have a₁:M m₁:=⟨ha₁,rfl⟩
  have a₂:M m₂:=⟨ha₂,by change inputScalar L m₂=inputScalar L m₁;unfold inputScalar;rw [←heq.1]⟩
  have hready:RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (Impl.Ed448.AArch64.Verify.hash v.callee) (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ (HashReady L H)):=by
    apply VG.Proof.Ed25519.AArch64.Whole.rel_wp
      ((hash_ct v hL ha₁ ha₂).mono (fun _ _ h => h) (fun _ _ _ => trivial))
    · intro t h
      exact WP.mono (hash_ok v hL h.1 ha₁) fun _ ⟨hu,hh⟩ => ⟨hu,hh⟩
    · intro t h
      refine WP.mono (hash_ok v hL h.1 ha₂) fun _ ⟨hu,hh⟩ => ⟨hu,?_⟩
      change Spec.Sha3.bytesAt _ _ _=H
      rw [hh,←heq.2]
  have r := reduce_ct hV a₁ a₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := reduceArgs)
    (by decide) (by simp [reduceArgs, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fK, fH, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := HashReady L H) (reduceVal L)
    (fun _ hc _ p hp => by
      simp only [reduceArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · rfl
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (k_apart L)) (scr_writable L) (Q := EquationReady L.sig (L.E+BitVec.ofNat 64 fK) S K)
    (fun hM hc hp => WP.mono (reduce_step hL hc) fun u ⟨hu,hk⟩ => ⟨hu,by
      change _=S ∧ _=K
      exact ⟨(current_scalar hL hu).trans hM.2,by rw [hk,hp]⟩⟩)
  have q := equation_ct hQ hV ⟨rfl,rfl⟩ a₁ a₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := equationArgs)
    (by decide) (by simp [equationArgs, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, aPk, aSig, fK, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (equationVal L) S K
    (fun hm hc _ p hp => by
      simp only [equationArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact arg_src hL hc.1 hm.1 (j := 0) (by decide) _
      · exact arg_src hL hc.1 hm.1 (j := 5) (by decide) _
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) hL.pc hL.sc (fr_scr hL (by decide)) hL.nc
    (in_readable L.PK (by simp [Lay.inputs])) (in_readable L.SIG (by simp [Lay.inputs]))
    (.inl ⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩) (scr_writable L) (fun h => h.1.2)
  exact (e.seq (hready.seq (r.seq q))).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem lay_eq {s t : State} (hp : vLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5, h6, hsy,_⟩ := hp
  simp only [lay, VG.Proof.Ed25519.AArch64.Whole.base, sp, h0, h1, h2, h3, h4, h5, h6, hsy]

private theorem entry_bytes {s p:State} (h:vLocal.pre s)
    (hp:VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    PublicBytes {s with mem:=p.mem} s:=by
  obtain ⟨_,_,_,_,_,_,kp,kx,km,ks,_⟩:=h
  have hf:=VG.Proof.Ed25519.AArch64.Whole.saved_frame hp
  have hw:Frame [below s.sp 352] s.mem p.mem:=Frame.sub hf (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_,List.mem_singleton_self _,below_sub (by decide) (by decide)⟩)
  exact ⟨frame_bytes (R:=⟨s.gpr .x0,57⟩) hw kp (Nat.le_refl 57) (by change (57:Nat)≤2^64;decide),
    frame_bytes hw kx (Nat.le_refl _) (Nat.le_of_lt (s.gpr .x2).isLt),
    frame_bytes hw km (Nat.le_refl _) (Nat.le_of_lt (s.gpr .x4).isLt),
    frame_bytes (R:=⟨s.gpr .x5,114⟩) hw ks (Nat.le_refl 114) (by change (114:Nat)≤2^64;decide)⟩

private theorem entry_eqInputs {s t p q:State} (hs:vLocal.pre s) (ht:vLocal.pre t)
    (hpa:VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p)
    (hqb:VG.Proof.Ed25519.AArch64.Whole.Saved (entered t) 6 q) (hp:vLocal.pub s t) :
    EqInputs (lay s) p.mem q.mem:=by
  obtain ⟨_,h0,h1,h2,h3,h4,h5,_,_,hb⟩:=hp
  have a:=entry_bytes hs hpa
  have b:=entry_bytes ht hqb
  have h:PublicBytes {s with mem:=p.mem} {t with mem:=q.mem}:=
    ⟨a.1.trans (hb.1.trans b.1.symm),a.2.1.trans (hb.2.1.trans b.2.1.symm),
      a.2.2.1.trans (hb.2.2.1.trans b.2.2.1.symm),a.2.2.2.trans (hb.2.2.2.trans b.2.2.2.symm)⟩
  simp only [PublicBytes,ed448_bytesAt] at h
  rw [←h0,←h1,←h2,←h3,←h4,←h5] at h
  refine ⟨h.2.2.2,?_⟩
  simp only [hashIn,lay]
  have hs57:=congrArg (List.take 57) h.2.2.2
  rw [take57',take57'] at hs57
  rw [h.1,h.2.1,h.2.2.1,hs57]

/-- The frame and its body, for a context shorter than 256 bytes. -/
theorem wrap_ct (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.Sparse.EqOk) :
    ConstantTime isa (fun s => vLocal.pre s ∧ (s.gpr .x2).toNat < 256) vLocal.pub
      (Impl.Ed25519.AArch64.Whole.wrap (body v.callee)) := by
  refine VG.Proof.Ed25519.AArch64.Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v hQ (lay_ok hs.1 hs.2) (entry_ctx hs.1 hp) (entry_args hs.1 hp) (entry_x6 hp)
      (entry_syms hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx0 (lay s) t.gpr t.v q.mem (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)) := he ▸ entry_ctx ht.1 hqb
    have hqa : Args (lay s) q.mem := he ▸ entry_args ht.1 hqb
    have hq6 : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).gpr .x6 = (lay s).scr := he ▸ entry_x6 hqb
    have hqs : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).syms Impl.Ed448.AArch64.Sparse.baseSym = (lay s).T :=
      he ▸ entry_syms hqb
    exact ⟨(body_ct v hQ (lay_ok hs.1 hs.2) (entry_args hs.1 hpa) hqa (entry_eqInputs hs.1 ht.1 hpa hqb hp) _ _ _ _ _ _
      ⟨⟨entry_ctx hs.1 hpa, entry_x6 hpa, entry_syms hpa⟩, ⟨hq, hq6, hqs⟩⟩ ea eb).1, trivial⟩

theorem verify_ct (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.Sparse.EqOk) :
    ConstantTime isa vLocal.pre vLocal.pub (verifyWith v.callee) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have hl := (RelCT.taint (A := taint) (P := fun s₁ s₂ => vLocal.pre s₁ ∧ vLocal.pre s₂ ∧ vLocal.pub s₁ s₂)
    (c := .block [.lsr .x .x9 .x2 8]) (Taint.ofRegs [.x2])
    (fun _ _ h => ⟨h.2.2.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst hr
      exact h.2.2.2.2.2.1⟩) (by taint_decide)).wpDep (F := LsrPost) fun s₁ s₂ _ => ⟨lsr_ok s₁, lsr_ok s₂⟩
  refine hl.seq (RelCT.ite (fun a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, h₁, h₂⟩ => ?_) ?_ ?_)
  · simp only [eval, State.read, h₁.1, h₂.1, hp.2.2.2.1]
  · intro a b ta tb a' b' ⟨⟨_, σ₁, σ₂, ⟨p₁, p₂, hp⟩, h₁, h₂⟩, hc⟩ ea eb
    have hz : ∀ {σ t : State}, LsrPost σ t → isa.eval (.zero .x .x9) t = some true →
        (t.gpr .x2).toNat < 256 := fun h hc => by
      rw [lsr_x2 h]
      refine (lsr_zero h).1 ?_
      simpa [eval, State.read] using hc
    have hc₂ : isa.eval (.zero .x .x9) b = some true := by
      rw [← hc]; simp only [eval, State.read, h₁.1, h₂.1, hp.2.2.2.1]
    exact ⟨wrap_ct v hQ _ _ _ _ _ _ ⟨lsr_pre p₁ h₁, hz h₁ hc⟩ ⟨lsr_pre p₂ h₂, hz h₂ hc₂⟩
      (lsr_pub hp h₁ h₂) ea eb, trivial⟩
  · exact VG.Proof.Ed25519.AArch64.Whole.block_rel
      (fun _ _ ⟨⟨_, _, _, ⟨_, _, hp⟩, h₁, h₂⟩, _⟩ => h₁.2.2.2.2.2.1.trans (hp.1.trans h₂.2.2.2.2.2.1.symm))
      (by taint_decide)

open VG.Impl.Ed448.AArch64.Sparse (baseSym baseWords baseConsts)
open VG.Proof.Ed448.AArch64.Sparse (baseWords_length satMem satMem_held)

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0 | .x3 => 0x3000 | .x4 => 0 | .x5 => 0x4000
    | .x6 => 0x6000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 114⟩, ⟨0x100000, 8192⟩]
  wr := [⟨0x6000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
      ⟨s.gpr .x5, 114⟩, ⟨s.syms baseSym, 8 * baseWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x6, 8192⟩])
    (hheld : ∀ i < baseWords.length,
      s.mem.readW (s.syms baseSym + BitVec.ofNat 64 (8 * i)) 64 = baseWords.getD i 0)
    (hfit : (s.syms baseSym).toNat + 8 * baseWords.length ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms baseSym, 8 * baseWords.length⟩ r)
    (hds : Region.Disjoint ⟨s.syms baseSym, 8 * baseWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hal : (s.syms baseSym).toNat % 64 = 0)
    (hrest : (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (⟨s.gpr .x5, 114⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 57⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x5, 114⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 114 ≤ 2 ^ 64 ∧
      (s.gpr .x6).toNat + 8192 ≤ 2 ^ 64) :
    (Spec.Ed448.verifyContract (AArch64.abi.withConsts baseConsts) 352).pre s := by
  sig_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
    Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
    VG.Proof.Ed448.AArch64.Sparse.baseConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14⟩ := hrest
  exact ⟨hsp, by rw [hrd]; rfl, hheld, hfit, hdw, hds, hal, by rw [hrd]; rfl, hw, r1, r2, r3, r4, r5, r6, r7,
    r8, r9, r10, r11, r12, r13, r14⟩

theorem sat : ∃ s, (Spec.Ed448.verifyContract (AArch64.abi.withConsts baseConsts) 352).pre s := by
  have hl := baseWords_length
  refine ⟨satState, spec_pre (by decide) (by rw [hl]; rfl) rfl satMem_held (by rw [hl]; decide) ?_
    (by rw [hl]; exact Region.disjoint_of_sep (by decide)) (by decide) ?_⟩
  · rw [hl]
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

private theorem byteMap_inj : ∀ {xs ys:List Byte},xs.map (·.toNat)=ys.map (·.toNat) → xs=ys
  | [],[],_ => rfl
  | a::xs,b::ys,h => by
    simp only [List.map_cons,List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1,byteMap_inj h.2]

theorem verify_implies : vLocal.Implies
    (Spec.Ed448.verifyContract (AArch64.abi.withConsts baseConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
      VG.Proof.Ed448.AArch64.Sparse.baseConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, -, ht, hw, pc, cc, mc, sc, kp, kx, km, ks, kc, np, -, -, ns, nc⟩ := h
    refine ⟨?_, hw, pc, cc, mc, sc, kp, kx, km, ks, kc, np, ns, nc, hsp, held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post s t _ h := by
    sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
      VG.Proof.Ed448.AArch64.Sparse.baseConsts_eq, Abi.withConsts]
    change t.gpr .x0 = _ at h
    rw [h]
    split <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
      VG.Proof.Ed448.AArch64.Sparse.baseConsts_eq, Abi.withConsts] at h
    obtain ⟨sp,hsy,bytes,h0,h1,h2,h3,h4,h5,h6⟩:=h
    have hb:=byteMap_inj bytes
    simp only [List.append_assoc] at hb
    obtain ⟨pk,rest⟩:=List.append_inj' hb (by simp [Spec.Ed448.bytesAt,h2,h4])
    obtain ⟨ctx,rest⟩:=List.append_inj' rest (by simp [Spec.Ed448.bytesAt,h4])
    obtain ⟨msg,sig⟩:=List.append_inj' rest (by simp [Spec.Ed448.bytesAt])
    exact ⟨sp,h0,h1,h2,h3,h4,h5,h6,hsy,pk,ctx,msg,sig⟩
  sat := sat

theorem verify_verified (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.Sparse.EqOk) :
    Verified AArch64.target (verifyWith v.callee)
      (Spec.Ed448.verifyContract (AArch64.abi.withConsts Impl.Ed448.AArch64.Sparse.baseConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verify_ok v hQ h) (verify_ct v hQ) (.refl verify_implies.sat_left))
    verify_implies

end VG.Proof.Ed448.AArch64.Verify
