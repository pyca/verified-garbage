module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: the pieces that keep `rsp`, MXCSR and the stack

Each piece but the RSA operation's call is `Good` (`Stack.lean`): its
instructions never write `rsp` or load MXCSR, the streaming hash functions
it calls indirectly keep MXCSR's control bits, and its calls nest at most
two deep.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (seqs round mgfXor xorOut initF updF finF)

theorem initF_good (sl : Nat) : Good (initF sl) := ⟨rfl, rfl, by simp [initF, Code.depth, Impl.Mgf1.X86_64.fnStack]⟩

theorem updF_good (sl : Nat) : Good (updF sl) := ⟨rfl, rfl, by simp [updF, Code.depth, Impl.Mgf1.X86_64.fnStack]⟩

theorem finF_good (sl : Nat) : Good (finF sl) := ⟨rfl, rfl, by simp [finF, Code.depth, Impl.Mgf1.X86_64.fnStack]⟩

theorem Good.seq {a b : Prog isa} (ha : Good a) (hb : Good b) : Good (.seq a b) :=
  ⟨by simp only [Code.allInstrs, ha.1, hb.1, Bool.and_self],
    by simp only [ctlOk, ha.2.1, hb.2.1, Bool.and_self, Bool.or_true],
    by simp only [Code.depth, Nat.max_le]; exact ⟨ha.2.2, hb.2.2⟩⟩

theorem Good.block' {is : List Instr} (h : (Code.block is : Prog isa).allInstrs okI = true)
    (hc : ctlOk (.block is) = true) : Good (.block is) :=
  ⟨h, hc, by simp [Code.depth]⟩

theorem hashLabel_good (o : Nat) : Good (hashLabel o) := by
  unfold hashLabel seqs seqs seqs seqs seqs
  exact .seq (.block' rfl rfl) (.seq (initF_good _) (.seq (.block' rfl rfl) (.seq (updF_good _)
    (.seq (.block' rfl rfl) (finF_good _)))))

theorem xorOut_good : Good (xorOut lay) := ⟨rfl, rfl, by simp [xorOut, seqs, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

theorem mgfXor_good : Good (mgfXor lay) := by
  have hr : Good (round lay) := by
    unfold round seqs seqs seqs seqs seqs seqs seqs seqs seqs
    exact .seq (.block' rfl rfl) (.seq (initF_good _) (.seq (.block' rfl rfl) (.seq (updF_good _)
      (.seq (.block' rfl rfl) (.seq (updF_good _) (.seq (.block' rfl rfl) (.seq (finF_good _)
        (.seq xorOut_good (.block' rfl rfl)))))))))
  exact .seq (.block' rfl rfl) ⟨hr.1, by simp only [ctlOk]; exact hr.2.1, by simp only [Code.depth]; exact hr.2.2⟩

theorem block_good (is : List Instr) (h : (Code.block is : Prog isa).allInstrs okI = true)
    (hc : ctlOk (.block is) = true) : Good (.block is) :=
  ⟨h, hc, by simp [Code.depth]⟩

/-- The shift of RSAES-OAEP's decryption, which RSASSA-PSS's verification uses too. -/
theorem shift_good : Good shift := ⟨rfl, rfl, by simp [shift, shiftPass, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

theorem clearEm_good : Good clearEm := ⟨rfl, rfl, by simp [clearEm, Code.depth]⟩

theorem putMsg_good : Good putMsg := ⟨rfl, rfl, by simp [putMsg, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

theorem zeroOut_good : Good zeroOut := ⟨rfl, rfl, by simp [zeroOut, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

theorem copySeed_good : Good copySeed :=
  ⟨rfl, rfl, by simp [copySeed, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

theorem copyLh_good : Good copyLh :=
  ⟨rfl, rfl, by simp [copyLh, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

theorem dbArgs_good : Good (.block dbArgs) := ⟨rfl, rfl, by simp [Code.depth]⟩

theorem seedArgs_good : Good (.block seedArgs) := ⟨rfl, rfl, by simp [Code.depth]⟩

theorem pubArgs_good : Good (.block pubArgs) := ⟨rfl, rfl, by simp [Code.depth]⟩

theorem lensH_good : Good (Impl.Dispatch.X86_64.chain (lens.map fun p => (p.1, .block (consts p.2)))) :=
  ⟨by decide, by decide, by decide⟩

theorem lensG_good : Good (Impl.Dispatch.X86_64.chain (lens.map fun p =>
    (p.1, .block [.mov32 .rax (im p.2), .store (Impl.Mgf1.X86_64.sp sGD) .rax]))) :=
  ⟨by decide, by decide, by decide⟩

/-- `selPrologueWith ls`, whose dispatches are `Good`. -/
theorem selPrologueWith_good {ls : List (Nat × Nat)}
    (hH : Good (Impl.Dispatch.X86_64.chain (ls.map fun p => (p.1, .block (consts p.2)))))
    (hG : Good (Impl.Dispatch.X86_64.chain (ls.map fun p =>
      (p.1, .block [.mov32 .rax (im p.2), .store (Impl.Mgf1.X86_64.sp sGD) .rax]))))
    (jH jG : Nat) : Good (selPrologueWith ls jH jG) := by
  unfold selPrologueWith seqs seqs seqs seqs
  exact .seq (.block' rfl rfl) (.seq hH (.seq (.block' rfl rfl) (.seq hG (.block' rfl rfl))))

theorem selPrologue_good (jH jG : Nat) : Good (selPrologue jH jG) :=
  selPrologueWith_good lensH_good lensG_good jH jG

theorem Good.all {c : Prog isa} (h : Good c) : c.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by
    rw [Code.allInstrs_eq]
    exact List.all_eq_true.mpr fun i hi => by rw [SpSafe.of_noSp h.noSp i hi]; rfl)

end VG.Proof.RsaOaep.X86_64
