module

public import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks

/-! # Loading the preceding ciphertext without overwriting the group -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.AesCfb.AArch64.Decrypt

/-- The first state is the chaining register; subsequent states precede their output. -/
theorem inputs_ok (b : VReg) (bs : List VReg) (s : State)
    (hnd : (b::bs).Nodup) (hlen : bs.length ≤ 4096)
    (hin : ∀ k < bs.length, InRegions (s.rd ++ s.wr)
      (s.gpr .x2 + BitVec.ofNat 64 (16*k)) 16) :
    WP isa (.block (inputs (b::bs))) s fun t =>
      t.v b = s.v .v31 ∧
      (∀ k (hk : k < bs.length), t.v bs[k] =
        s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16*k)) 128) ∧
      Fr [] (b::bs) s t := by
  rw [inputs, WP.block_cons_iff]
  refine ⟨s.setV b (s.v .v31), by simp [isa, exec, VOp.eval, BitVec.or_self], ?_⟩
  refine WP.mono (ldData_ok bs 0 (s.setV b (s.v .v31)) (List.nodup_cons.mp hnd).2 (by omega)
    (fun k hk => by simpa only [State.setV, Nat.zero_add] using hin k hk)) fun t ⟨hv,hf⟩ => ?_
  refine ⟨?_, ?_, ⟨?_, ?_, hf.sp, hf.mem, hf.rd, hf.wr⟩⟩
  · rw [hf.v _ (List.nodup_cons.mp hnd).1]
    simp [State.setV]
  · intro k hk
    simpa only [State.setV, Nat.zero_add] using hv k hk
  · intro r hr; exact hf.gpr r hr
  · intro r hr
    rw [hf.v r (fun h => hr (List.mem_cons_of_mem _ h))]
    exact setV_v_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))

end VG.Proof.AesCfb.AArch64.Decrypt
