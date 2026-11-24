module

/-! # The direction of a Camellia core on x86 (32-bit) -/

@[expose] public section

namespace VG.Impl.Camellia.X86

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

end VG.Impl.Camellia.X86
