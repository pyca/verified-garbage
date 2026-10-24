module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModExp
public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModArith
public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Round

/-!
# Finite-field Diffie–Hellman on PPC64LE: the domain operations

`vg_ffdh_check_public` (`Spec/Ffdh/Contract.lean`), in the working space of
RSA's public-key operation (`Impl/Bignum/PPC64LE/PublicChecked.lean`) at
`scratch`: a header of 32 words, then arrays of `w + 2` words, `w = ⌈p_len / 8⌉`,
with array 0 at `r10`, the arrays' size in `r29`, `2 w` in `r11` and the
working space in `r23` and `r31`. The nonvolatile registers are saved in the
header's words 14–31.

* p is loaded into array 0 and checked as `vg_rsa_public_precompute` checks
  a modulus (`Precompute.check`): odd, its first byte not zero, at least
  `2^511`; otherwise the result is 0;
* y into array 4 (`PublicChecked.loadX`), 1 into array 7, `p − 1` into
  array 6 (`subMod`, array 7 the modulus), 0 into array 5; the mask of
  `y < p` is `subMod`'s, and those of `y = 0`, `y = 1` and `y = p − 1` are
  `eqMask`'s (as in the Miller–Rabin round);
* with q: `R² mod p` into array 1 (`Precompute.r2`), `-p⁻¹ mod 2³²` into
  `r12` (`PublicChecked.minv`), `y^q mod p` into array 4 by
  `ModExp.powSecret` over q's `p_len` octets, and `eqMask` with 1, again in
  array 7.

Everything is public, and the code branches on p's validity, y's range and
whether there is q.

Registers kept throughout: `r21` `domain`, `r26` `y` and then the mask of
y's range, `r27` `domain_len`, `r28` `p_len`.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.MillerRabin.PPC64LE (eqMask)

/-! ## Saving the nonvolatile registers -/

/-- The nonvolatile registers saved, `r23` (which keeps the working space's
address) last. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31,
    .r23].getD i .r14

/-- The byte offset of saved register `i` in the header. -/
def saveOff (i : Nat) : Nat := 112 + 8 * i

/-- Save them in the working space at `ws`, and keep its address in `r23`. -/
def save (ws : Reg) : List Instr :=
  (List.range 18).flatMap (fun i => [.store .d (saved i) ws (saveOff i)]) ++ [.addi .r23 ws 0]

/-- Restore them, through `r23`, which is restored last. -/
def restore : List Instr :=
  (List.range 17).flatMap (fun i => [.load .d (saved i) .r23 (saveOff i)]) ++ [.load .d .r23 .r23 (saveOff 17)]

/-! ## The domain -/

/-- `domain` (`r3`), `domain_len` (`r4`) and `p_len` (`r5`) kept, `2 w`, the
arrays' size, array 0's base, and the working space in `r31`. -/
def setup : List Instr :=
  [.addi .r21 .r3 0, .addi .r27 .r4 0, .addi .r28 .r5 0, .addi .r11 .r5 7, .lsr .d .r11 .r11 3,
    .lsl .r29 .r11 3, .addi .r29 .r29 16, .addi .r10 .r23 hdrBytes, .lsl .r11 .r11 1, .addi .r31 .r23 0]

/-- p into array 0, and `r0 := 0` exactly when it is a valid modulus. -/
def loadP : Prog isa :=
  .seq (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) (.seq Precompute.loadN Precompute.check)

/-- 1 into array 7, `p − 1` into array 6 and 0 into array 5. -/
def consts : Prog isa :=
  .seq PublicChecked.one (.seq (.block (base .r8 0 ++ base .r9 6 ++ base .r10 7))
    (.seq subMod (.seq (.block ([.addi .r10 .r23 hdrBytes] ++ base .r14 5)) Precompute.zeroWords)))

/-- `r26 &= ¬r19`. -/
def clear19 : List Instr := [.logic .or .r26 .r26 .r19, .logic .xor .r26 .r26 .r19]

/-- y (`r26`) into array 4, then `r26 :=` all ones if `1 < y < p − 1`, else 0. -/
def range : Prog isa :=
  .seq (.block [.addi .r9 .r26 0]) (.seq PublicChecked.loadX (.seq consts
    (.seq (.block (base .r8 4 ++ base .r9 3)) (.seq subMod (.seq (.block [.addi .r26 .r20 0])
      (.seq (eqMask .r19 4 5) (.seq (.block clear19) (.seq (eqMask .r19 4 7) (.seq (.block clear19)
        (.seq (eqMask .r19 4 6) (.block clear19)))))))))))

/-- `r0 := 0` exactly when `domain_len = 3 p_len`: there is q. -/
def hasQ : List Instr := [.lsl .r0 .r28 1, .add .r0 .r0 .r28, .sub .r0 .r27 .r0]

/-- `r3 := 1` if `y^q mod p = 1`, else 0: `R² mod p`, `-p⁻¹`, the power by
q's octets (at `domain + 2 p_len`), compared with 1 in array 7. -/
def subgroup : Prog isa :=
  .seq (.block (base .r5 1 ++ base .r8 2 ++ base .r9 3)) (.seq Precompute.r2
    (.seq (.block (PublicChecked.minv ++ [.lsl .r30 .r28 1, .add .r30 .r30 .r21, .addi .r31 .r28 0]))
      (.seq ModExp.powSecret (.seq (.block [.addi .r31 .r23 0]) (.seq PublicChecked.one (.seq (eqMask .r3 4 7)
        (.block [.li .r0 1, .logic .and .r3 .r3 .r0])))))))

/-- The check of y, after p's. -/
def checkY : Prog isa :=
  .seq range (.ite (.zero .d .r26) (.block [.li .r3 0])
    (.seq (.block hasQ) (.ite (.zero .d .r0) subgroup (.block [.li .r3 1]))))

/-- `vg_ffdh_check_public(domain, domain_len, p_len, y, y_len, scratch,
scratch_len)`. -/
def checkPublic : Prog isa :=
  .seq (.block (save .r8 ++ setup ++ [.addi .r26 .r6 0])) (.seq loadP
    (.seq (.ite (.zero .d .r0) checkY (.block [.li .r3 0])) (.block restore)))

/-! ## `vg_ffdh_check_domain` -/

/-- `r26 := domain + p_len`, g's octets. -/
def gPtr : List Instr := [.add .r26 .r21 .r28]

/-- `r26 := domain + 2 p_len`, q's octets. -/
def qPtr : List Instr := [.lsl .r26 .r28 1, .add .r26 .r26 .r21]

/-- `r26 &=` the mask of q's last octet being odd. -/
def qOdd : List Instr :=
  [.lsl .r16 .r28 1, .add .r16 .r16 .r28, .add .r16 .r16 .r21, .subi .r16 .r16 1, .lbz .r0 .r16 0, .li .r3 1,
    .logic .and .r0 .r0 .r3, .li .r3 0, .sub .r0 .r3 .r0, .logic .and .r26 .r26 .r0]

/-- p's octets into array 0 again. -/
def reloadP : Prog isa :=
  .seq (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) Precompute.loadN

/-- `r25 :=` the mask of `p mod q = 1`: q into array 0, p's octets reduced
modulo q into array 1 (`ModArith.reduce`), compared with 1; then p back into
array 0. -/
def qDiv : Prog isa :=
  .seq (.block [.lsl .r12 .r28 1, .add .r12 .r12 .r21, .addi .r6 .r28 0]) (.seq Precompute.loadN
    (.seq (.block [.addi .r30 .r21 0, .addi .r31 .r28 0]) (.seq ModArith.reduce
      (.seq (.block [.addi .r31 .r23 0]) (.seq PublicChecked.one (.seq (eqMask .r25 1 7) reloadP))))))

/-- g's octets into array 4, `r26 :=` the mask of `1 < g < p − 1`. -/
def checkG : Prog isa := .seq (.block gPtr) range

/-- With q. -/
def withQ : Prog isa :=
  .seq (.block qPtr) (.seq range (.seq (.block qOdd) (.ite (.zero .d .r26) (.block [.li .r3 0])
    (.seq qDiv (.seq checkG (.seq (.block [.logic .and .r26 .r26 .r25])
      (.ite (.zero .d .r26) (.block [.li .r3 0]) subgroup)))))))

/-- Without q. -/
def withoutQ : Prog isa :=
  .seq checkG (.ite (.zero .d .r26) (.block [.li .r3 0]) (.block [.li .r3 1]))

/-- The checks after p's. -/
def domainBody : Prog isa :=
  .seq (.block hasQ) (.ite (.zero .d .r0) withQ withoutQ)

/-- `vg_ffdh_check_domain(domain, domain_len, p_len, scratch, scratch_len)`. -/
def checkDomain : Prog isa :=
  .seq (.block (save .r6 ++ setup)) (.seq loadP
    (.seq (.ite (.zero .d .r0) domainBody (.block [.li .r3 0])) (.block restore)))

end VG.Impl.Ffdh.PPC64LE.Domain
