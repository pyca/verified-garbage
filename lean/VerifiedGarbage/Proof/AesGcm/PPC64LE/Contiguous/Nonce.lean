module

-- separate module: The 96-bit nonce path keeps the initialized counter words live in registers.

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Contiguous
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOne
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.Contiguous
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame

/-! # Preparing J₀ and its successor together on POWER -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Contiguous
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt inc32 ofBytes)
open VG.Proof.Cmac (le4 store4)
open VG.WriteBytes

variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
include L

private theorem short_wp {H : Block} {Np : Addr} {s : State} (h : J0In V sp H Np 12 s) :
    WP isa (.block (j012 ++ initState12)) s (J0Out V sp H (bytesAt s.mem Np 12) s.mem) := by
  apply WP.block_append
  refine WP.mono (j012_regs_ok L h) fun u ⟨mid,a,b,c⟩ => ?_
  have st := mid.env.r30
  have w0 := mid.env.perm.stW (show 48 + 4 ≤ 80 by decide)
  have w1 := mid.env.perm.stW (show 52 + 4 ≤ 80 by decide)
  have w2 := mid.env.perm.stW (show 56 + 4 ≤ 80 by decide)
  have w3 := mid.env.perm.stW (show 60 + 4 ≤ 80 by decide)
  have z0 := mid.env.perm.stW (show 16 + 8 ≤ 80 by decide)
  have z1 := mid.env.perm.stW (show 24 + 8 ≤ 80 by decide)
  have iv : bytesAt s.mem Np 12 =
      le4 (s.mem.readW Np 32) ++ le4 (s.mem.readW (Np + BitVec.ofNat 64 4) 32) ++
        le4 (s.mem.readW (Np + BitVec.ofNat 64 8) 32) := by
    rw [Proof.Cmac.le4_readW,Proof.Cmac.le4_readW,Proof.Cmac.le4_readW]
    rw [show (12 : Nat) = 4 + 8 from rfl,bytesAt_add,show (8 : Nat) = 4 + 4 from rfl,bytesAt_add,
      add_ofNat_assoc,List.append_assoc]
  have cnt : ofBytes (le4 ((u.gpr .r3).setWidth 32) ++ le4 ((u.gpr .r4).setWidth 32) ++
      le4 ((u.gpr .r5).setWidth 32) ++ le4 (0x02000000 : BitVec 32)) =
      inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np 12)) := by
    rw [a,b,c,Proof.Gcm.j0_12 _ (length_bytesAt _ _ _),iv,← le4_one,ofBytes_le4,ofBytes_le4,inc32_words]
    rfl
  apply WP.of_runBlock
  simp only [initState12,runBlock_cons,runStep_some,runBlock_nil,exec,addr,State.store,State.write,Size.bytes,
    st,w0,w1,w2,w3,z0,z1,write_4,write_8,Option.bind_some,Option.some.injEq,
    exists_eq_left',reduceCtorEq,ne_eq,not_false_eq_true,Nat.reduceLT,Nat.reducePow,Nat.reduceMod,
    ↓reduceIte,and_self,implies_true]
  refine initWords_ok L mid cnt ?_ ?_ ⟨rfl,rfl,rfl,rfl⟩
  · simp only [store4,add_ofNat_assoc,Nat.reduceAdd]; rfl
  · intro r _ _ _ n6 _ n8; simp [n6,n8]

omit L in
private theorem check_wp {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In V sp H Np n s) :
    WP isa (.block [.subi .r6 .r25 12]) s fun t =>
      J0In V sp H Np n t ∧ t.gpr .r6 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ t.mem = s.mem := by
  have h₁ : WP isa (.block [.subi .r6 .r25 12]) s fun s₁ =>
      s₁.gpr .r6 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ (∀ r, r ≠ .r6 → s₁.gpr r = s.gpr r) ∧
        Keeps s s₁ := by
    crun [h.r25]
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono h₁ fun s₁ ⟨h6, hg₁, hk₁⟩ => ?_
  have hi : J0In V sp H Np n s₁ :=
    ⟨h.env.keep (fun r hr => hg₁ r (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, by rw [hk₁.mem]; exact h.hH,
      by rw [hg₁ _ (by decide)]; exact h.r24, by rw [hg₁ _ (by decide)]; exact h.r25, h.r18,
      h.data.of_eq hk₁.rd hk₁.wr⟩
  exact ⟨hi,h6,hk₁.mem⟩

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem nonce_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In V sp H Np n s) :
    WP isa nonceC s (J0Out V sp H (bytesAt s.mem Np n) s.mem) := by
  have hlt := h.data.lt
  refine WP.seq (WP.mono (check_wp h) fun t ⟨hi,h6,mem⟩ => ?_)
  rw [← mem]
  refine WP.ite (decide (n = 12)) (eval_subk h6 hlt (by decide)) (fun ht => ?_) (fun hf => ?_)
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact short_wp L hi
  · exact WP.seq (WP.mono (j0hash_ok L hi (by simpa using hf)) fun _ hm => initState_ok L hm)


omit L in
theorem nonce_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] {c st w sp np : Addr} {n : Nat} (lay : Lay c st w) :
    CT (J0I c st w sp np n) nonceC := by
  let pre := fun t => J0I c st w sp np n t ∧ t.gpr .r6 = BitVec.ofNat 64 n - BitVec.ofNat 64 12
  refine CT.seq (J := pre) ?_ (fun t ⟨v,h,k,r,z,hi⟩ => WP.mono (check_wp hi) fun _ ⟨a,b,_⟩ =>
    ⟨⟨v,h,k,r,z,a⟩,b⟩) ?_
  · exact CT.taint [] (fun _ _ ⟨_,_,_,_,_,a⟩ ⟨_,_,_,_,_,b⟩ =>
      ⟨a.env.sp.trans b.env.sp.symm,by simp⟩) (by taint_decide)
  refine CT.ite (decide (n = 12)) (fun _ ⟨⟨_,_,_,_,_,a⟩,e⟩ => eval_subk e a.data.lt (by decide))
    (fun _ => ?_) (fun hn => ?_)
  · refine CT.taint [.r24,.r30] (fun _ _ ⟨⟨_,_,_,st1,_,p⟩,_⟩ ⟨⟨_,_,_,st2,_,q⟩,_⟩ =>
      ⟨p.env.sp.trans q.env.sp.symm,?_⟩) (by taint_decide)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · rw [p.r24,q.r24]
    · rw [p.env.r30,q.env.r30,st1,st2]
  · refine CT.seq (J := J0M c st w sp) ((j0hash_ct lay).mono fun _ h => h.1)
      (fun t ⟨⟨v,h,k,r,z,hi⟩,_⟩ => WP.mono (j0hash_ok (lay.v k r z) hi (by simpa using hn))
        fun _ mid => ⟨v,h,_,_,k,r,z,mid⟩) ?_
    refine CT.taint [.r30] (fun _ _ ⟨_,_,_,_,_,st1,_,p⟩ ⟨_,_,_,_,_,st2,_,q⟩ =>
      ⟨p.env.sp.trans q.env.sp.symm,?_⟩) (by taint_decide)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [p.env.r30,q.env.r30,st1,st2]

end VG.Proof.AesGcm.PPC64LE.Contiguous
