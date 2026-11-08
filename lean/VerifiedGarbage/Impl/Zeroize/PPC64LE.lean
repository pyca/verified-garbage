module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Zeroization: PPC64LE implementation

`vg_zeroize(p = r3, len = r4)`: eight doubleword stores (`std`) a loop
iteration while 64 bytes are left, then doubleword stores, then a byte tail
(`stb`). Stores to normal memory may be unaligned. The loops count down to
zero, and only `p` and `len` decide the branches and addresses.
-/

@[expose] public section

namespace VG.Impl.Zeroize.PPC64LE
open VG.PPC64LE

def step (word : Bool) : List Instr :=
  [if word then .store .d .r5 .r3 0 else .stb .r5 .r3 0,
   .addi .r3 .r3 (if word then 8 else 1), .subi .r6 .r6 1]

def loop (word : Bool) : Prog isa :=
  .ite (.zero .d .r6) (.block []) (.loop (.block (step word)) (.nonzero .d .r6))

/-- The `m` doublewords at `r3` zeroed, without moving `r3`. -/
def stores (m : Nat) : List Instr := (List.range m).map fun j => .store .d .r5 .r3 (8 * j)

/-- 64 bytes zeroed, and on to the next. -/
def wide : List Instr := stores 8 ++ [.addi .r3 .r3 64, .subi .r6 .r6 1]

def wideLoop : Prog isa := .ite (.zero .d .r6) (.block []) (.loop (.block wide) (.nonzero .d .r6))

def zeroize : Prog isa :=
  .seq (.block [.li .r5 0, .lsr .d .r6 .r4 6])
    (.seq wideLoop
      (.seq (.block [.li .r7 63, .logic .and .r6 .r4 .r7, .lsr .d .r6 .r6 3])
        (.seq (loop true) (.seq (.block [.li .r7 7, .logic .and .r6 .r4 .r7]) (loop false)))))

end VG.Impl.Zeroize.PPC64LE
