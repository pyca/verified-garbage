module

/-! # The domain checker parameter generation calls

Generation's own arithmetic (the generator search and this check) is a few
public exponentiations, against the many Miller–Rabin rounds its
probable-prime calls run: it multiplies with the baseline round's inlined
Montgomery multiplication on every backend, so one checker serves them all. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.SharedChecker

def name : String := "vg_dsa_generation_check_parameters"

end VG.Proof.Dsa.X86_64.Generation.SharedChecker
