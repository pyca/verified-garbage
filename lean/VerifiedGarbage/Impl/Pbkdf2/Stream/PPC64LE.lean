module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE

/-!
# PBKDF2-HMAC over any streaming hash function: PPC64LE implementation

`iterate(key = r3, u = r4, n = r5, t = r6, scratch = r7)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` of PBKDF2's step 3, with the HMAC key given as
the two streaming states that HMAC's `init` leaves at `key` (`K₀ ⊕ ipad`,
then `K₀ ⊕ opad`), for any hash function whose streaming functions HMAC's
code calls (`VG.Impl.Hmac.Stream.PPC64LE.Hash`).

Each step is HMAC's `finalize` over a copy of the inner key state, with the
same calls of the streaming functions: it copies the inner key state into
`scratch` (`st`), absorbs `U` with `update`, finalizes into `dig`, copies the
outer key state's hash value over `st`'s (which then represents the outer
block), absorbs the inner digest, finalizes into `ub`, whose first `D` bytes
are the new `U`, and exclusive-ors them into `T`. `U` is copied into `ub`
first, since `u` is read-only.

`scratch` holds the working space of the functions we call (`W` bytes), our
caller's `r20`–`r25` (`Hash.saveAt`), then `st`, `dig` and `ub`. Our variables
live in `r20`–`r23`, which none of the functions we call writes: `r20` =
`key`, `r21` = `scratch`, `r22` = the steps left and `r23` = `t`. `n` is a
32-bit argument whose other bits may be anything: it is zero-extended into
`r22` first. Every address and branch depends only on the pointers and `n`.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Stream.PPC64LE

open VG.PPC64LE
open VG.Impl.MdStream.PPC64LE (mov)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.Hmac.Stream.PPC64LE.Hash (cp32)

namespace Iter

variable (H : Hash)

/-- Where the working streaming state is in `scratch`. -/
def st : Nat := H.W + 48

/-- Where the inner digest goes. -/
def dig : Nat := st H + H.S

/-- Where `U` is (`FD` bytes, of which `U` is the first `D`). -/
def ub : Nat := dig H + H.FD

/-- The bytes of `iterate`'s working space. -/
def bytes : Nat := ub H + H.FD

/-- `U` copied from `u` (`r4`) into `ub`. -/
def copyU : List Instr := (List.range (H.D / 4)).flatMap (cp32 .r4 .r21 0 (ub H))

/-- The inner key state copied into `st`. -/
def copyKey : List Instr := (List.range (H.S / 4)).flatMap (cp32 .r20 .r21 0 (st H))

/-- The outer key state's hash value copied over `st`'s. -/
def copyHV : List Instr := (List.range (H.N / 4)).flatMap (cp32 .r20 .r21 H.S (st H))

/-- Word `k` of `ub` exclusive-ored into `t`. -/
def xor32 (k : Nat) : List Instr :=
  [.load .w .r8 .r23 (4 * k), .load .w .r9 .r21 (ub H + 4 * k), .logic .xor .r8 .r8 .r9,
    .store .w .r8 .r23 (4 * k)]

/-- `T ← T ⊕ U`. -/
def xorT : List Instr := (List.range (H.D / 4)).flatMap (xor32 H)

/-- `update` of `st` from a `count` of `B`, with the `D` bytes at `src`. -/
def updD (src : Nat) : List Instr :=
  [.addi .r3 .r21 (st H), .li .r4 H.B, .addi .r5 .r21 src, .li .r6 H.D, mov .r7 .r21]

/-- `finalize` of `st`, with a `count` of `B + D`, into `dst`. -/
def finD (dst : Nat) : List Instr :=
  [.addi .r3 .r21 (st H), .li .r4 (H.B + H.D), .addi .r5 .r21 dst, mov .r6 .r21]

/-- One step. -/
def step : Prog isa :=
  .seq (.block (copyKey H ++ updD H (ub H))) (.seq H.callUpd
  (.seq (.block (finD H (dig H))) (.seq H.callFin
  (.seq (.block (copyHV H ++ updD H (dig H))) (.seq H.callUpd
  (.seq (.block (finD H (ub H))) (.seq H.callFin
    (.block (xorT H ++ [.subi .r22 .r22 1])))))))))

end Iter

variable (H : Hash)

/-- `n` zero-extended into `r22`. -/
def zextN : List Instr := [.lsl .r22 .r5 32, .lsr .d .r22 .r22 32]

/-- `iterate`, but for saving the link register. -/
def iterateMain : Prog isa :=
  .seq (.block (Hash.saveAt H.W .r7 ++ zextN ++ [mov .r20 .r3, mov .r21 .r7, mov .r23 .r6] ++
      Iter.copyU H))
  (.seq (.ite (.zero .d .r22) (.block []) (.loop (Iter.step H) (.nonzero .d .r22)))
    (.block (Hash.restoreAt H.W)))

/-- PBKDF2's `iterate` with its working space as an argument. -/
def iterate : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) (iterateMain H) (.pop .r0)) (.block [.mtlr .r0]))

end VG.Impl.Pbkdf2.Stream.PPC64LE
