import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailContract

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

def satState (wlen olen : Nat) : State where
  gpr r := match r with
    | .x0=>0x1000 | .x1=>0x2000 | .x2=>0x3000 | .x3=>0x4000
    | .x4=>0x6000 | .x6=>0x7000 | _=>0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,64⟩,⟨0x2000,wlen⟩,⟨0x6000,64⟩]
  wr := [⟨0x3000,olen⟩,⟨0x4000,2048⟩,⟨0x7000,1024⟩]

theorem implies {wlen olen : Nat} (hw : wlen=768 ∨ wlen=1024) (ho : olen=48 ∨ olen=64) :
    (kernel wlen olen).Implies (commitTailContract AArch64.abi wlen olen) := by
  refine { pre := fun _ h => shared_pre hw ho h, post := ?_,pub := ?_,sat := ?_ }
  · sig_implies_post [commitTailContract,commitTailSig,kernel,seedBytes,commitTailSeed,AArch64.abi,AArch64.argRegs]
  · intro s t _ _ h
    sig_pub [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs] at h
    sig_split h
    refine ⟨by with_reducible assumption,?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption
  · refine ⟨satState wlen olen,?_⟩
    rcases hw with rfl|rfl <;> rcases ho with rfl|rfl
    all_goals
      sig_pre [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs]
      sig_and_intros
    all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide

theorem verified65 : Verified AArch64.target
    (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48) (commitTailContract AArch64.abi 768 48) :=
  Verified.of_correct (fun s hp => correct s hp) (fun s t l r a b _ _ hp hs ht => code65_ct s t l r a b trivial trivial hp hs ht)
    (implies (.inl rfl) (.inl rfl))

theorem verified87 : Verified AArch64.target
    (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64) (commitTailContract AArch64.abi 1024 64) :=
  Verified.of_correct (fun s hp => correct s hp) (fun s t l r a b _ _ hp hs ht => code87_ct s t l r a b trivial trivial hp hs ht)
    (implies (.inr rfl) (.inr rfl))

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
