module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Prefetch
public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Store

/-! One pipelined block, including its guarded lookahead and in-place store. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem step_ok {s₀ s : State} {k : Nat} (hp : UPre s₀) (hk : k < N s₀) (h : Inv s₀ k s) :
    WP isa (Impl.AesCbc.AArch64.Encrypt.step (R s₀)) s (Inv s₀ (k+1)) := by
  rw [Impl.AesCbc.AArch64.Encrypt.step]
  refine WP.seq (WP.mono (first4_ok hp hk h) fun a ⟨ca,ra⟩ => ?_)
  refine WP.seq (WP.mono (prefetch_ok hp (by omega) ca) fun b ⟨cb,fb,nb⟩ => ?_)
  have rb : RInv chainRegs (wK s₀) (fun _ => st (input s₀ k)) 5 b := by
    intro r hr
    have hr' : r=.v31 := List.mem_singleton.mp hr
    subst hr'
    rw [fb.v _ (by decide)]
    exact ra _ hr
  rw [WP.block_append_iff]
  have h6 : 6 ≤ R s₀ := by have := hp.rounds; omega
  refine WP.mono (rounds_ok cb.env.keys rb (R s₀-6) (by omega)) fun c ⟨rc,fc⟩ => ?_
  have cc := cb.vframe fc (by decide)
  have nc : k+1 < N s₀ → c.v .v0=s₀.mem.readW (blk s₀ (k+1)) 128 ^^^ c.v .v7 := by
    rw [fc.v _ (by decide),fc.v _ (by decide)]
    exact nb
  rw [show 5+(R s₀-6)=R s₀-1 by omega] at rc
  rw [show Impl.AesCbc.AArch64.Encrypt.finish=
    [.vop (.aese .v31 .v29)]++[.vop (.logic .eor .v1 .v31 .v30),.strq .v1 .x2 0,.addImm .x .x2 .x2 16]
      from rfl,WP.block_append_iff]
  refine WP.mono (last_ok cc.env.keys rc) fun d ⟨rd,fd⟩ => ?_
  have cd := cc.vframe fd (by decide)
  refine store_advance_ok hp hk cd rd ?_
  rw [fd.v _ (by decide),fd.v _ (by decide)]
  exact nc
end VG.Proof.AesCbc.AArch64.Encrypt
