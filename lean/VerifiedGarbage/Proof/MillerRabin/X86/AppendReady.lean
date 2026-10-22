module

public import VerifiedGarbage.Proof.MillerRabin.X86.TableInitTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.HeaderReady

/-! # Carry the public table cursor through multiplication and copying -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

structure AppendReady (σ : State) (base : Addr) (bytes w n : Nat) (s : State) : Prop where
  stage : Stage base bytes w σ s
  count : w32 s.mem base sK = 14 - n
  cursor : s.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w (13 + n))

structure TransferReady (σ : State) (base : Addr) (bytes w n : Nat) (s : State) : Prop where
  stage : Stage base bytes w σ s
  count : w32 s.mem base sK = 14 - n
  dest : s.gpr .ebx = ptr32 base (arrAt w (13 + n)) + BitVec.ofNat 32 (8 * w)

theorem table_product_ready {σ s : State} {base : Addr} {bytes w n : Nat}
    (facts : RoundFacts σ base bytes w) (h : TableState σ base bytes w n s) :
    WP isa (product 6 6 5) s (AppendReady σ base bytes w n) := by
  refine WP.mono (facts.multiply (o := 6) (a := 6) (b := 5) h.stage (by decide) (by decide)
    (by decide) (.inr (.inl rfl)) (by rw [h.witness]; exact facts.witness)) ?_
  rintro t ⟨_, stage, _, frame⟩
  refine ⟨stage, (congrArg BitVec.toNat (product_frame_header h.stage.context h.stage.room facts.fit
    (by decide) (by decide : sK + 4 ≤ 256) frame)).trans h.count, ?_⟩
  have eq := congrArg (BitVec.setWidth 32) (product_frame_stack h.stage.context h.stage.room facts.fit
    (by decide) (by decide : tableCursor + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes) frame)
  change t.mem.readW (off (byteAddr (s.gpr .esp)) tableCursor) 32 =
    s.mem.readW (off (byteAddr (s.gpr .esp)) tableCursor) 32 at eq
  rw [h.stage.stack] at eq
  exact eq.trans h.cursor

theorem table_transfer_ready {σ s : State} {base : Addr} {bytes w n : Nat}
    (facts : RoundFacts σ base bytes w) (h : AppendReady σ base bytes w n s) (hn : n < 14) :
    WP isa tabTransfer s (TransferReady σ base bytes w n) := by
  refine WP.mono (table_transfer h.stage facts.lower facts.upper facts.fit ⟨by omega, by omega⟩
    facts.width h.cursor) ?_
  rintro t ⟨stage, result⟩
  have bound : base.toNat + arrAt w (13 + n) < 2 ^ 32 := by
    have fit := array_fits_bytes facts.fit (by omega : 13 + n < 28)
    have nw := h.stage.context.ws.nowrap
    have lower := facts.lower
    omega
  have frame := result.frame
  rw [ptr32_addr bound] at frame
  have count := array_frame_header h.stage.context.ws.nowrap facts.fit (by omega : 13 + n < 28)
    (by decide : sK + 4 ≤ 256) frame
  exact ⟨stage, (congrArg BitVec.toNat count).trans h.count, result.dest⟩

end VG.Proof.MillerRabin.X86
