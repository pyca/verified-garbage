module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
public import VerifiedGarbage.Impl.Dsa.X86.CombKey
import VerifiedGarbage.Proof.Framework.X86.AllocFrame

/-! Inlining a cdecl body adds no observable trace beyond the body's execution. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86

theorem inlineInvoke_trace {body : Prog isa} {s t : State} {rd wr : List Region} {tr : List Leak}
    (reads : Covers (rd++wr) (s.rd++s.wr)) (writes : Covers wr s.wr)
    (terminates : WP isa body ((allocated 4 s).withRegions rd wr) (fun _ => True))
    (E : Exec isa (VG.Impl.Dsa.X86.Comb.invoke body) s tr t) :
    ∃ u, Exec isa body ((allocated 4 s).withRegions rd wr) tr u := by
  cases E with
  | frame push run pop =>
    have eq := alloc_some push
    subst eq
    have readWide : Covers (rd++wr) ((allocated 4 s).rd++(allocated 4 s).wr) :=
      reads.trans (Covers.append (Covers.refl _) (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr))
    have writeWide : Covers wr (allocated 4 s).wr :=
      writes.trans (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr)
    obtain ⟨trace,u,Run,_⟩ := terminates
    obtain ⟨rfl,_⟩ := Exec.det run (regionModel.inline Run readWide writeWide).1
    exact ⟨u,by simpa only [isa,addrs,List.map_nil,List.nil_append,List.append_nil] using Run⟩

end VG.Proof.Dsa.X86.KeyRandom
