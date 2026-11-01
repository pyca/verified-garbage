module

public import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Gathering a list of slices, PPC64LE: the loop

`gather` copies the `cnt` slices that the descriptors at `r7` list, one after
the other, to `r9` (`gather_wp`): with `i` of them copied, `r7` is at
descriptor `i`, `r8` holds `cnt - i`, `r9` is `gatheredLen` of the first `i`
past `dst`, and the memory is the one on entry with their concatenation
(`gathered`) written at `dst`. The descriptors and the slices are apart from
`dst`, so they are what they were on entry. As on AArch64
(`Proof/AesGcm/AArch64/Gather/Loop.lean`).
-/

@[expose] public section

namespace VG.Proof.Gather.PPC64LE

open VG VG.PPC64LE VG.Impl.Gather.PPC64LE VG.WriteBytes
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd wp_ld wp_addi wp_subi)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)

/-- The registers the gathering writes. -/
abbrev gatherRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9]

/-- What the gathering keeps: the other registers, the stack pointer, the
link register and the permissions. -/
structure GKeeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ gatherRegs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  lr : t.lr = s.lr
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem GKeeps.refl (s : State) : GKeeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem GKeeps.trans {s t u : State} (h₁ : GKeeps s t) (h₂ : GKeeps t u) : GKeeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.sp.trans h₁.sp, h₂.lr.trans h₁.lr,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem gkeeps_of_keeps {s t : State} (h : Keeps s t) : GKeeps s t :=
  ⟨fun r hr => h.gpr r fun hm => hr (by
    simp only [copyRegs, gatherRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with e | e | e | e | e | e <;> simp [e]), h.sp, h.lr, h.rd, h.wr⟩

theorem gkeeps_of_upd {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v)
    (hd : d ∈ gatherRegs := by decide) : GKeeps s t :=
  ⟨fun r hr => u.other r fun e => hr (e ▸ hd), u.sp, u.lr, u.rd, u.wr⟩

section
variable (m : Mem) (Src : Addr)

/-- Slice `i`: its address and its length. -/
abbrev sb (i : Nat) : Addr := m.readW (Src + BitVec.ofNat 64 (16 * i)) 64
abbrev sl (i : Nat) : Nat := (m.readW (Src + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) 64).toNat

end

theorem desc_off (i : Nat) : i * (2 * (64 / 8)) = 16 * i := by omega

theorem gl_succ (m : Mem) (Src : Addr) (i : Nat) :
    gatheredLen 64 m Src (i + 1) = gatheredLen 64 m Src i + sl m Src i := by
  rw [Proof.Gcm.gatheredLen_succ, desc_off]

theorem pt_succ (m : Mem) (Src : Addr) (i : Nat) :
    gathered 64 m Src (i + 1) = gathered 64 m Src i ++ bytesAt m (sb m Src i) (sl m Src i) := by
  rw [Proof.Gcm.gathered_succ, desc_off, BitVec.setWidth_eq]

theorem gl_mono (m : Mem) (Src : Addr) {i j : Nat} (h : i ≤ j) :
    gatheredLen 64 m Src i ≤ gatheredLen 64 m Src j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · rw [gl_succ]; exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

/-- Slice `i` is listed. -/
theorem slice_mem (m : Mem) (Src : Addr) {i cnt : Nat} (hi : i < cnt) :
    (⟨sb m Src i, sl m Src i⟩ : Region) ∈ Sig.listed 64 m .u8 Src cnt := by
  simp only [Sig.listed, List.mem_map, List.mem_range]
  refine ⟨i, hi, ?_⟩
  simp only [desc_off, BitVec.setWidth_eq, Elem.size, Nat.mul_one]

/-- What the gathering needs: `cnt` descriptors at `Src`, listing slices of
`L` bytes in all, to copy to `Dst`, apart from them. -/
structure GatherPre (t : State) (Src Dst : Addr) (cnt L : Nat) : Prop where
  r7 : t.gpr .r7 = Src
  r8 : t.gpr .r8 = BitVec.ofNat 64 cnt
  r9 : t.gpr .r9 = Dst
  hcnt : cnt < 2 ^ 64
  dw : Src.toNat + cnt * 16 ≤ 2 ^ 64
  lt : L < 2 ^ 64
  len : gatheredLen 64 t.mem Src cnt = L
  dsr : Covers [⟨Src, cnt * 16⟩] (t.rd ++ t.wr)
  lsr : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, Covers [r] (t.rd ++ t.wr)
  dw' : Covers [⟨Dst, L⟩] t.wr
  dsd : (⟨Src, cnt * 16⟩ : Region).Disjoint ⟨Dst, L⟩
  lsd : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, r.Disjoint ⟨Dst, L⟩

/-- The loop's invariant: the first `i` slices copied. -/
structure GInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  r7 : u.gpr .r7 = Src + BitVec.ofNat 64 (16 * i)
  r8 : u.gpr .r8 = BitVec.ofNat 64 (cnt - i)
  r9 : u.gpr .r9 = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

/-- After `next`: descriptor `i` loaded. -/
structure NInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  r7 : u.gpr .r7 = Src + BitVec.ofNat 64 (16 * (i + 1))
  r8 : u.gpr .r8 = BitVec.ofNat 64 (cnt - i)
  r9 : u.gpr .r9 = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  r3 : u.gpr .r3 = sb t.mem Src i
  r4 : u.gpr .r4 = BitVec.ofNat 64 (sl t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

theorem GInv.init {t : State} {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    GInv t t Src Dst cnt 0 :=
  ⟨by rw [h.r7]; exact (BitVec.add_zero _).symm, by rw [h.r8, Nat.sub_zero],
    by rw [h.r9]; simp [gatheredLen, Sig.listed], by simp [gathered, Sig.listed, writeBytes_nil],
    GKeeps.refl t⟩

section
variable {t u : State} {Src Dst : Addr} {cnt L i : Nat} (h : GatherPre t Src Dst cnt L)
include h

omit h in
/-- What the loop has written is within `dst`. -/
theorem frame_of {xs : List Byte} (hm : u.mem = writeBytes t.mem Dst xs) (hx : xs.length ≤ L) :
    Frame [⟨Dst, L⟩] t.mem u.mem := by
  rw [hm]
  refine writeBytes_frame t.mem Dst _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]
  omega

theorem gl_le (hi : i ≤ cnt) : gatheredLen 64 t.mem Src i ≤ L := h.len ▸ gl_mono t.mem Src hi

theorem len_le (hi : i ≤ cnt) : (gathered 64 t.mem Src i).length ≤ L :=
  (Proof.Gcm.length_gathered _ _ _ _) ▸ gl_le h hi

/-- The descriptors are what they were. -/
theorem desc_of (hf : Frame [⟨Dst, L⟩] t.mem u.mem) (d : Nat) (hd : d + 8 ≤ cnt * 16) :
    u.mem.readW (Src + BitVec.ofNat 64 d) 64 = t.mem.readW (Src + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨Src, cnt * 16⟩) (Offset.contains_base Src hd (by have := h.dw; omega))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.dsd) (by decide)

theorem next_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.block next) u (NInv t · Src Dst cnt i) := by
  have hdw := h.dw
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  have hin (d : Nat) (hd : d + 8 ≤ cnt * 16) : InRegions (u.rd ++ u.wr) (Src + BitVec.ofNat 64 d) 8 := by
    rw [hu.keep.rd, hu.keep.wr]
    exact h.dsr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base Src hd (by omega)⟩
  have ha8 : Src + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8 = Src + BitVec.ofNat 64 (16 * i + 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  unfold next
  refine wp_ld (a := Src + BitVec.ofNat 64 (16 * i)) (by decide) (by decide)
    (by rw [hu.r7]; exact BitVec.add_zero _) (hin _ (by omega)) fun u₁ v₁ => ?_
  refine wp_ld (a := Src + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [v₁.other _ (by decide), hu.r7]) (by rw [v₁.rd, v₁.wr, ha8]; exact hin _ (by omega))
    fun u₂ v₂ => ?_
  refine wp_addi (by decide) (by decide) fun u₃ v₃ => WP.block_nil ?_
  have m₂ : u₁.mem = u.mem := v₁.mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hu.keep.trans ((gkeeps_of_upd v₁).trans ((gkeeps_of_upd v₂).trans
    (gkeeps_of_upd v₃)))⟩
  · rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), hu.r7, BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.mul_succ]
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hu.r8]
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hu.r9]
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, desc_of h hfr _ (by omega)]
  · rw [v₃.other _ (by decide), v₂.gpr, m₂, ha8, desc_of h hfr _ (by omega), ← ha8, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [v₃.mem, v₂.mem, m₂, hu.mem]

theorem rest_wp (hi : i < cnt) (hu : NInv t u Src Dst cnt i) :
    WP isa (.seq copySlice (.block [.subi .r8 .r8 1])) u (GInv t · Src Dst cnt (i + 1)) := by
  have hc := h.hcnt
  have hL := h.lt
  have hgl : gatheredLen 64 t.mem Src (i + 1) ≤ L := gl_le h (by omega)
  have hlen : (gathered 64 t.mem Src i).length = gatheredLen 64 t.mem Src i := Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ] at hgl
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  -- The slice.
  have hmem := slice_mem t.mem Src hi
  have hsd : (⟨sb t.mem Src i, sl t.mem Src i⟩ : Region).Disjoint ⟨Dst, L⟩ := h.lsd _ hmem
  have hsub : (⟨Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i), sl t.mem Src i⟩ : Region).Sub ⟨Dst, L⟩ :=
    Offset.sub_base _ hgl
  have hsp : SlicePre u (sb t.mem Src i) (Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)) (sl t.mem Src i) :=
    ⟨hu.r3, hu.r9, hu.r4, by omega, by rw [hu.keep.rd, hu.keep.wr]; exact h.lsr _ hmem,
      by rw [hu.keep.wr]; exact covers_off h.dw' hgl hL, hsd.sub_right hsub⟩
  refine WP.seq (WP.mono (copySlice_wp u hsp) fun u₂ ⟨m₂, r9₂, kp₂⟩ => ?_)
  refine wp_subi (by decide) (by decide) fun u₃ v₃ => WP.block_nil ?_
  -- The slice's bytes were what they were on entry.
  have hbytes : bytesAt u.mem (sb t.mem Src i) (sl t.mem Src i) =
      bytesAt t.mem (sb t.mem Src i) (sl t.mem Src i) := by
    refine bytesAt_frame hfr (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd
  refine ⟨?_, ?_, ?_, ?_, hu.keep.trans ((gkeeps_of_keeps kp₂).trans (gkeeps_of_upd v₃))⟩
  · rw [v₃.other _ (by decide), kp₂.gpr _ (by decide), hu.r7]
  · rw [v₃.gpr, kp₂.gpr _ (by decide), hu.r8, ofNat_sub_one (by omega), Nat.sub_sub]
  · rw [v₃.other _ (by decide), r9₂, BitVec.add_assoc, ← BitVec.ofNat_add, ← gl_succ]
  · rw [v₃.mem, m₂, hbytes, hu.mem, pt_succ, ← hlen,
      writeBytes_append _ _ _ _ (by rw [hlen, Proof.Cmac.bytesAt_length]; omega)]

end

/-- `gatherLoop`: the `cnt ≥ 1` slices copied to `Dst`. -/
theorem gatherLoop_advance_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hpos : 1 ≤ cnt) :
    WP isa gatherLoop t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' ∧ t'.gpr .r7=Src+BitVec.ofNat 64 (16*cnt) := by
  have hc := h.hcnt
  refine WP.loop (M := isa) (c := .nonzero .d .r8)
    (fun (w : Nat) (u : State) => ∃ i, w = cnt - i ∧ i < cnt ∧ GInv t u Src Dst cnt i) ?_ (cnt - 0) _
    ⟨0, rfl, hpos, GInv.init h⟩
  rintro w u ⟨i, rfl, hi, hu⟩
  refine WP.seq (WP.mono (next_wp h hi hu) fun u₁ h₁ => WP.mono (rest_wp h hi h₁) fun u₃ h₃ => ?_)
  have ev := eval_nonzero (r := .r8) (a := cnt - (i + 1)) h₃.r8 (by omega)
  by_cases he : i + 1 = cnt
  · left
    exact ⟨by rw [ev]; simp [he], by rw [h₃.mem, he], h₃.keep,by rw [h₃.r7,he]⟩
  · right
    exact ⟨by rw [ev]; simp; omega, cnt - (i + 1), by omega, i + 1, rfl, by omega, h₃⟩

/-- `gather`: the `cnt` slices copied to `Dst`. -/
theorem gather_advance_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa gather t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' ∧ t'.gpr .r7=Src+BitVec.ofNat 64 (16*cnt) := by
  refine WP.ite (decide (cnt = 0)) (eval_zero h.r8 h.hcnt) (fun ht => ?_) (fun hf => ?_)
  · have h0 : cnt = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by simp [gathered, Sig.listed, writeBytes_nil], GKeeps.refl t,by change t.gpr .r7=Src+0#64; rw [BitVec.add_zero]; exact h.r7⟩
  · have h0 : cnt ≠ 0 := by simpa using hf
    exact gatherLoop_advance_wp t h (by omega)


/-- `gatherLoop`, forgetting the final descriptor pointer. -/
theorem gatherLoop_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hpos : 1≤cnt) :
    WP isa gatherLoop t fun t' => t'.mem=writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' :=
  WP.mono (gatherLoop_advance_wp t h hpos) fun _ ht => ⟨ht.1,ht.2.1⟩

/-- `gather`, forgetting the final descriptor pointer. -/
theorem gather_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa gather t fun t' => t'.mem=writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' :=
  WP.mono (gather_advance_wp t h) fun _ ht => ⟨ht.1,ht.2.1⟩

end VG.Proof.Gather.PPC64LE
