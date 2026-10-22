module

public import VerifiedGarbage.Proof.MillerRabin.X86.Copy
public import VerifiedGarbage.Proof.MillerRabin.X86.StageFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Preserve live operands across writes to other arrays or header words -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem array_frame_num {m m' : Mem} {base : Addr} {bytes w a o : Nat}
    (nw : base.toNat + bytes ≤ 2 ^ 32) (hf : arrAt w 28 ≤ bytes)
    (ha : a < 28) (ho : o < 28) (hne : a ≠ o)
    (F : Frame [⟨off base (arrAt w o), 8 * w⟩] m m') :
    numAt m' base w a = numAt m base w a := by
  have fa := array_fits_bytes hf ha
  have fo := array_fits_bytes hf ho
  unfold numAt
  rw [F.read (r := ⟨off base (arrAt w a), 8 * w⟩) (Region.contains_self _ _)
    (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (arrays_apart w hne) (by omega) (by omega)) (by omega)]

theorem header_frame_num {m m' : Mem} {base : Addr} {bytes w a d : Nat}
    (nw : base.toNat + bytes ≤ 2 ^ 32) (hf : arrAt w 28 ≤ bytes)
    (ha : a < 28) (hd : d + 4 ≤ 256)
    (F : Frame [⟨off base d, 4⟩] m m') :
    numAt m' base w a = numAt m base w a := by
  have fa := array_fits_bytes hf ha
  have lo : 256 ≤ arrAt w a := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes]; omega
  unfold numAt
  rw [F.read (r := ⟨off base (arrAt w a), 8 * w⟩) (Region.contains_self _ _)
    (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by omega)]

theorem stack_header_frame_num {s : State} {m m' : Mem} {base : Addr} {bytes w a d : Nat}
    (ctx : ProtectedContext s base bytes) (hf : arrAt w 28 ≤ bytes)
    (ha : a < 28) (hd : d + 4 ≤ 256)
    (F : Frame [⟨off (byteAddr (s.gpr .esp)) VG.Impl.MillerRabin.X86.tableCursor, 4⟩,
      ⟨off base d, 4⟩] m m') : numAt m' base w a = numAt m base w a := by
  have fa := array_fits_bytes hf ha
  have nw := ctx.ws.nowrap
  have lo : 256 ≤ arrAt w a := Nat.le_add_right _ _
  unfold numAt
  rw [F.read (r := ⟨off base (arrAt w a), 8 * w⟩) (Region.contains_self _ _)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (ctx.apart.sub_left (Offset.sub_base _ (by omega))).sub_right
          (Offset.sub_base _ (by decide))
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by omega)]

theorem array_frame_header {m m' : Mem} {base : Addr} {bytes w o d : Nat}
    (nw : base.toNat + bytes ≤ 2 ^ 32) (hf : arrAt w 28 ≤ bytes)
    (ho : o < 28) (hd : d + 4 ≤ 256)
    (F : Frame [⟨off base (arrAt w o), 8 * w⟩] m m') :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  have fo := array_fits_bytes hf ho
  have lo : 256 ≤ arrAt w o := Nat.le_add_right _ _
  exact F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _)
    (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide)

theorem workspace_frame_word {m m' : Mem} {base : Addr} {bytes d o n : Nat}
    (nw : base.toNat + bytes ≤ 2 ^ 32) (hd : d + 4 ≤ bytes) (ho : o + n ≤ bytes)
    (apart : d + 4 ≤ o ∨ o + n ≤ d)
    (F : Frame [⟨off base o, n⟩] m m') : m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _)
    (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ apart (by omega) (by omega)) (by decide)

theorem readW_of_w32 {m : Mem} {base : Addr} {d n : Nat} (hn : n < 2 ^ 32)
    (h : w32 m base d = n) : m.readW (off base d) 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  exact h

theorem headers_frame_num {m m' : Mem} {base : Addr} {bytes w a : Nat} {ds : List Nat}
    (nw : base.toNat + bytes ≤ 2 ^ 32) (hf : arrAt w 28 ≤ bytes) (ha : a < 28)
    (bounds : ∀ d ∈ ds, d + 4 ≤ 256)
    (F : Frame (ds.map (fun d => ⟨off base d, 4⟩)) m m') :
    numAt m' base w a = numAt m base w a := by
  have fa := array_fits_bytes hf ha
  have lo : 256 ≤ arrAt w a := Nat.le_add_right _ _
  unfold numAt
  rw [F.read (r := ⟨off base (arrAt w a), 8 * w⟩) (Region.contains_self _ _)
    (by
      intro r hr
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
      have := bounds d hd
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by omega)]

theorem headers_frame_word {m m' : Mem} {base : Addr} {bytes d : Nat} {ds : List Nat}
    (nw : base.toNat + bytes ≤ 2 ^ 32) (hd : d + 4 ≤ bytes)
    (bounds : ∀ k ∈ ds, k + 4 ≤ bytes)
    (apart : ∀ k ∈ ds, d + 4 ≤ k ∨ k + 4 ≤ d)
    (F : Frame (ds.map (fun k => ⟨off base k, 4⟩)) m m') :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _)
    (by
      intro r hr
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      have := bounds k hk
      exact Offset.disjoint _ (apart k hk) (by omega) (by omega)) (by decide)

end VG.Proof.MillerRabin.X86
