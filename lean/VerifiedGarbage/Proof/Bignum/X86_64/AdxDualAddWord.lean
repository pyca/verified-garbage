import VerifiedGarbage.Impl.Bignum.X86_64.AdxDualAdd
import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep

namespace VG.Proof.Bignum.X86_64.AdxDualAdd
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

theorem word_ok (s : State) {dst : Reg} {a b : Src} {va vb : BitVec 64} {c o : Bool}
    (ha : readSrc s a = some va)
    (hb : ∀ t, Keeps [dst] s t → readSrc t b = some vb)
    (hia : ∀ n, a ≠ .imm n) (hib : ∀ n, b ≠ .imm n)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxDualAdd.word dst a b)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr dst).toNat + 2^64*(c'.toNat+o'.toNat) =
        (s.gpr dst).toNat + va.toNat + vb.toNat + c.toNat + o.toNat ∧ Keeps [dst] s t := by
  rw [show AdxDualAdd.word dst a b = ([.adcx dst a] : List Instr) ++ [.adox dst b] from rfl,
    WP.block_append_iff]
  refine WP.mono (adcx_ok s ha hia hc) fun u ⟨cu,hcu,hou,eu,ku⟩ => ?_
  refine WP.mono (adox_ok u (hb u ku) hib (hou.trans ho)) fun t ⟨ot,hot,hct,et,kt⟩ => ?_
  exact ⟨cu,ot,hct.trans hcu,hot,by omega,(ku.trans kt).mono (by simp)⟩

end VG.Proof.Bignum.X86_64.AdxDualAdd
