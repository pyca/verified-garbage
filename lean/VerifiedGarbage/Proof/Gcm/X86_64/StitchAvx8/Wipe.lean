module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Tail
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The keystream wiped

`ksWipe` stores a register it zeroes to the keystream `ksTail` leaves at
`scratch + 832` (`ksWipe_ok`): it writes nothing else, and leaves every
general register, so `EPost`, `DPost` and `EPostTo` hold after it as before
(`EPost.ksWipe`, `DPost.ksWipe`, `EPostTo.ksWipe`). What it stores does not
matter to the proofs.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (ksWipe)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Spec.Gcm (blockAt blocksAt)
open VG.Proof.Aes.X86_64.AesNi (ea_at)

/-- The first `n` of the eight stores of `xmm3` at `scratch + 832`. -/
theorem zeroStores_ok (s : State) (p : Addr) (hr11 : s.gpr .r11 = p)
    (hin : ∀ i < 8, InRegions s.wr (p + BitVec.ofNat 64 (832 + 16 * i)) 16)
    (hwrap : p.toNat + 1024 ≤ 2 ^ 64) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).map fun i =>
      .vmovdquStore .l128 (at_ .r11 (832 + 16 * i)) .xmm3)) s fun t =>
      Frame [⟨p + BitVec.ofNat 64 832, 128⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  | 0, _ => WP.block_nil ⟨Frame.refl _ _, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zeroStores_ok s p hr11 hin hwrap n (by omega)) fun t ⟨f, g, rd, wr⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    have ea : t.ea (at_ .r11 (832 + 16 * n)) = p + BitVec.ofNat 64 (832 + 16 * n) := by
      rw [ea_at, BitVec.ofInt_natCast, g, hr11]
    have hw : InRegions t.wr (p + BitVec.ofNat 64 (832 + 16 * n)) 16 := by rw [wr]; exact hin n (by omega)
    rw [WP.block_cons_iff]
    refine ⟨t.setMem (t.mem.writeW (p + BitVec.ofNat 64 (832 + 16 * n)) (t.xmm .xmm3)),
      by simp only [isa, exec, State.store128_eq, ea, hw, ite_true], WP.block_nil ⟨?_,
        by rw [State.setMem_gpr, g], by rw [State.setMem_rd, rd], by rw [State.setMem_wr, wr]⟩⟩
    simp only [State.setMem_mem]
    exact f.writeW (List.mem_singleton_self _) _ (Offset.contains p (by omega) (by omega) (by omega))

/-- `ksWipe`: the 128 bytes at `scratch + 832` written, nothing else, and
the general registers kept. -/
theorem ksWipe_ok (s : State) (p : Addr) (hr11 : s.gpr .r11 = p)
    (hin : ∀ i < 8, InRegions s.wr (p + BitVec.ofNat 64 (832 + 16 * i)) 16)
    (hwrap : p.toNat + 1024 ≤ 2 ^ 64) :
    WP isa (.block ksWipe) s fun t =>
      Frame [⟨p + BitVec.ofNat 64 832, 128⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [ksWipe, WP.block_cons_iff]
  let s' := (VOp.vbin VBinOp.vpxor VLen.l128 XReg.xmm3 XReg.xmm3 XReg.xmm3).exec s
  have h11 : s'.gpr .r11 = p := hr11
  have hin' : ∀ i < 8, InRegions s'.wr (p + BitVec.ofNat 64 (832 + 16 * i)) 16 := hin
  exact ⟨s', rfl, WP.mono (zeroStores_ok s' p h11 hin' hwrap 8 (by decide)) fun _ ⟨f, g, rd, wr⟩ => ⟨f, g, rd, wr⟩⟩

theorem blocksAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) : blocksAt m' p n = blocksAt m p n := by
  simp only [blocksAt]
  refine List.map_congr_left fun i hi => VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf fun r hr =>
    (hd r hr).sub_left (Offset.sub_base p (by simp at hi; omega))

theorem blockAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p :=
  VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf hd

/-- `c` then a block, then more of it. -/
theorem seq_block_append {c : Prog isa} {a b : List Instr} {s : State} {Q R : State → Prop}
    (h : WP isa (.seq c (.block a)) s Q) (hb : ∀ t, Q t → WP isa (.block b) t R) :
    WP isa (.seq c (.block (a ++ b))) s R := by
  rw [WP.seq_iff] at h ⊢
  exact WP.mono h fun t ht => WP.block_append_iff.mpr (WP.mono ht hb)

theorem ksR_sub (s₀ : State) : Region.Sub (ksR s₀) (pR s₀) := Offset.sub_base _ (by decide)

/-- `ksWipe` after the encryption keeps `EPost`. -/
theorem EPost.ksWipe {s₀ t : State} (hp : SPre s₀) (h : EPost s₀ t) :
    WP isa (.block ksWipe) t fun u => EPost s₀ u ∧ Frame [ksR s₀] t.mem u.mem := by
  have r11 : t.gpr .r11 = pp s₀ := h.gpr _ (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (ksWipe_ok t (pp s₀) r11 (fun i hi => by rw [h.wr]; exact in_sub hp.p_in (by omega))
    hp.wrap_p) fun u ⟨f, g, rd, wr⟩ => ⟨?_, f⟩
  have hd : blocksAt u.mem (dp s₀) (nb s₀) = blocksAt t.mem (dp s₀) (nb s₀) :=
    blocksAt_frame' f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hp.d_p.sub_right (ksR_sub s₀))
  exact ⟨by rw [hd]; exact h.data,
    by rw [blockAt_frame' f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact (hp.p_c.sub_left (ksR_sub s₀)).symm)]; exact h.ctr,
    by rw [blockAt_frame' f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact (hp.p_y.sub_left (ksR_sub s₀)).symm), hd]; exact h.y,
    h.frame.trans (f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact ⟨pR s₀, by simp, ksR_sub s₀⟩),
    fun r h1 h2 h3 h4 => by rw [g]; exact h.gpr r h1 h2 h3 h4, by rw [rd]; exact h.rd, by rw [wr]; exact h.wr⟩

/-- `ksWipe` after the decryption keeps `DPost`. -/
theorem DPost.ksWipe {s₀ t : State} (hp : SPre s₀) (h : DPost s₀ t) :
    WP isa (.block ksWipe) t (DPost s₀) := by
  have r11 : t.gpr .r11 = pp s₀ := h.gpr _ (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (ksWipe_ok t (pp s₀) r11 (fun i hi => by rw [h.wr]; exact in_sub hp.p_in (by omega))
    hp.wrap_p) fun u ⟨f, g, rd, wr⟩ => ?_
  have hd : blocksAt u.mem (dp s₀) (nb s₀) = blocksAt t.mem (dp s₀) (nb s₀) :=
    blocksAt_frame' f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact hp.d_p.sub_right (ksR_sub s₀))
  exact ⟨by rw [hd]; exact h.data,
    by rw [blockAt_frame' f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact (hp.p_c.sub_left (ksR_sub s₀)).symm)]; exact h.ctr,
    by rw [blockAt_frame' f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact (hp.p_y.sub_left (ksR_sub s₀)).symm)]; exact h.y,
    h.frame.trans (f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact ⟨pR s₀, by simp, ksR_sub s₀⟩),
    fun r h1 h2 h3 h4 => by rw [g]; exact h.gpr r h1 h2 h3 h4, by rw [rd]; exact h.rd, by rw [wr]; exact h.wr⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
