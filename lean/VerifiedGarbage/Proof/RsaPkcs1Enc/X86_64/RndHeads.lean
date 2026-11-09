module

-- separate module: its proofs build in parallel with `RndContract` and `RndCTScan`, which `RndCT` also imports

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndCorrect
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86-64: the blocks that load slots

What the blocks that load the frame's slots into registers leave there
(`statusHead_ok`, `zeroHead_ok`, `budgetHead_ok`): the constant-time proof
makes these registers public after each block, since they hold public data.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem statusHead_ok {s u : State} (hp : RPre s) {i : Nat} {ps : List Byte} (h : AfterCall s u i ps) :
    WP isa (.block status) u fun v => v.gpr .rdi = off (fb s) oBuf ∧
      v.gpr .rcx = BitVec.ofNat 64 (psLen s) ∧ v.gpr .r10 = BitVec.ofNat 64 0 := by
  have hF := fb_toNat hp
  have hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  xrun [status, h.rsp, off_buf, ea_sp, fb_off, hs.ld (d := oPs) (by decide),
    show u.mem.readW (off (fb s) oPs) 64 = word u.mem (fb s) oPs from rfl, h.slots.sPs]

theorem zeroHead_ok {s t : State} (hp : RPre s) (hsp : t.gpr .rsp = fb s)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hsl : Slots s t.mem) :
    WP isa (.block [.mov .rdi (.mem (sp oOut)), .mov .r10 (.mem (sp oK)), .mov32 .rax (.imm 0)]) t
      fun u => u.gpr .rdi = s.gpr .rdi ∧ u.gpr .r10 = s.gpr .r8 := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  xrun [ea_sp, hsp, fb_off, hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide),
    show t.mem.readW (off (fb s) oOut) 64 = word t.mem (fb s) oOut from rfl,
    show t.mem.readW (off (fb s) oK) 64 = word t.mem (fb s) oK from rfl, hsl.sOut, hsl.sK]

theorem budgetHead_ok {s t : State} (hp : RPre s) (hsp : t.gpr .rsp = fb s)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hsl : Slots s t.mem) (h11 : t.gpr .r11 = stackArg s 4) :
    WP isa (.block budget) t fun u => u.gpr .r10 = BitVec.ofNat 64 (cap s) ∧ u.gpr .r8 = s.gpr .rdx ∧
      u.cf = some (decide ((stackArg s 4).toNat < cap s)) ∧ u.gpr .r11 = stackArg s 4 := by
  have hF := fb_toNat hp
  have hP := hp.ps
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hcap : BitVec.ofNat 64 (psLen s) + BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (cap s) := by
    rw [show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 by decide, ← BitVec.ofNat_add]; rfl
  have hcapN : (BitVec.ofNat 64 (cap s)).toNat = cap s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by unfold cap Spec.RsaPkcs1Enc.padEntropy; omega)
  have hcf : decide ((stackArg s 4).toNat < (BitVec.ofNat 64 (cap s)).toNat) =
      decide ((stackArg s 4).toNat < cap s) := by rw [hcapN]
  xrun [budget, ea_sp, hsp, fb_off, hs.ld (d := oPs) (by decide), hs.ld (d := oTape) (by decide),
    show t.mem.readW (off (fb s) oPs) 64 = word t.mem (fb s) oPs from rfl,
    show t.mem.readW (off (fb s) oTape) 64 = word t.mem (fb s) oTape from rfl, hsl.sPs, hsl.sTape,
    hcap, h11, hcf]

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd
