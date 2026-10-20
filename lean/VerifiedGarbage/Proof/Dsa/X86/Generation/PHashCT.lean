module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.PHash
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedAddStructure
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHash
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHash
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedAddStructure

/-! # Wrapped-seed hashing depends only on public buffer pointers and the chosen hash -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Impl.Dsa.X86.Generation

structure PHashPublic where
  source : BitVec 32
  hash : HashPublic

structure PHashAt {H : Hash} (K : HashOK H) (len : Nat) (p : PHashPublic) (s : State) : Prop where
  resources : HashResources K p.hash.input p.hash.output p.hash.scratch len s
  esp : s.gpr .esp = p.hash.sp
  esi : s.gpr .esi = p.source
  edi : s.gpr .edi = p.hash.input
  edx : s.gpr .edx = p.hash.output
  ebp : s.gpr .ebp = p.hash.scratch

theorem PHashAt.keep {H : Hash} {K : HashOK H} {len : Nat} {p : PHashPublic} {s t : State}
    (R : PHashAt K len p s) (K' : Keeps [.eax, .ecx] s t) : PHashAt K len p t :=
  ⟨R.resources.keeps K' (by decide), (K'.1 _ (by decide)).trans R.esp,
    (K'.1 _ (by decide)).trans R.esi, (K'.1 _ (by decide)).trans R.edi,
    (K'.1 _ (by decide)).trans R.edx, (K'.1 _ (by decide)).trans R.ebp⟩

theorem pSeedAdd_ct {H : Hash} (K : HashOK H) (len : Nat) (width : len = 20 ∨ len = 32) :
    RelCT isa (Two (PHashAt K len)) (seedAdd len) (Two (PHashAt K len)) := by
  intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
  have regs : RegistersAgree [.esi, .edi] s t := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hs.esi.trans ht.esi.symm, hs.edi.trans ht.edi.symm]
  exact ⟨(seedAdd_ct len width _ _ _ _ _ _ regs es et).1,
    p, hs.keep (seedAdd_keeps es), ht.keep (seedAdd_keeps et)⟩

theorem pHashArgs_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (PHashAt K len)) (.block pHashArgs) (Two fun (p : PHashPublic) => HashAt K len p.hash) := by
  refine two_piece [] (by intro _ _ _ _ _ r hr; cases hr) (by taint_decide) ?_
  intro p s R
  refine WP.mono pHashArgs_ok fun t ⟨si, di, _, K'⟩ => ?_
  exact ⟨R.resources.keeps K' (by decide), (K'.1 _ (by decide)).trans R.esp,
    si.trans R.edi, di.trans R.edx, (K'.1 _ (by decide)).trans R.ebp⟩

theorem pSeedHash_ct {H : Hash} (K : HashOK H) (len : Nat) (width : len = 20 ∨ len = 32) :
    RelCT isa (Two (PHashAt K len)) (pSeedHash H len) (fun _ _ => True) :=
  RelCT.seq (pSeedAdd_ct K len width) (RelCT.seq (pHashArgs_ct K len)
    (two_map PHashPublic.hash (fun _ _ h => h) (seedHash_ct K len)))
end VG.Proof.Dsa.X86.Generation
