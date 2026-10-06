import VerifiedGarbage.Proof.Ed448.X86.Shake.Layout
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Impl.Ed448.X86.Shake

/-!
# Ed448 on x86 (32-bit): the header of `dom4`

`Kit.hdr_ok`: the block `hdrAt j off` leaves `"SigEd448" ‖ 0 ‖ ctxlen`, the
first ten bytes of `dom4(0, context)`, in the frame at `off`, `ctxlen` the
caller's argument `j` (below 256): three little-endian words, the last
`ctxlen · 2^8`, by eight doublings (`hdr_bytes`). It writes nothing else.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86 VG.X86.Wp VG.Impl.Ed448.X86.Shake
open VG.Impl.Ed25519.X86.Whole (at_)
open VG.Proof.Ed25519.X86 (Whole.Ctx Whole.FR)

/-- `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (c : BitVec 32) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat]

theorem bytes4 (m : Mem) (p : Addr) : Spec.Ed448.bytesAt m p 4 = Proof.X25519.leBytes 4 (m.readW p 32).toNat := by
  rw [Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_leBytes]; simp [Mem.readW]

/-- The bytes of the three words of the header, the last `w = ctxlen · 2^8`. -/
theorem hdr_bytes (m : Mem) (p : Addr) (c w : BitVec 32) (hw : w.toNat = c.toNat * 256) :
    Spec.Ed448.bytesAt (((m.writeW (p + BitVec.ofNat 64 8) w).writeW p 0x45676953#32).writeW
      (p + BitVec.ofNat 64 4) 0x38343464#32) p 10 = hdrBytes c := by
  generalize hM : ((m.writeW (p + BitVec.ofNat 64 8) w).writeW p 0x45676953#32).writeW
      (p + BitVec.ofNat 64 4) 0x38343464#32 = M
  have s84 : Mem.Sep (p + BitVec.ofNat 64 8) 4 (p + BitVec.ofNat 64 4) 4 := Offset.sep p (by omega) (by omega) (by omega)
  have s80 : Mem.Sep (p + BitVec.ofNat 64 8) 4 p 4 := by
    have := Offset.sep p (d := 8) (n := 4) (e := 0) (k := 4) (by omega) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have s04 : Mem.Sep p 4 (p + BitVec.ofNat 64 4) 4 := by
    have := Offset.sep p (d := 0) (n := 4) (e := 4) (k := 4) (by omega) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have h0 : M.readW p 32 = 0x45676953#32 := by
    rw [← hM, Mem.readW_writeW_sep s04 (by decide), Mem.readW_writeW_self32]
  have h1 : M.readW (p + BitVec.ofNat 64 4) 32 = 0x38343464#32 := by
    rw [← hM, Mem.readW_writeW_self32]
  have h2 : M.readW (p + BitVec.ofNat 64 8) 32 = w := by
    rw [← hM, Mem.readW_writeW_sep s84 (by decide), Mem.readW_writeW_sep s80 (by decide),
      Mem.readW_writeW_self32]
  have e10 : Spec.Ed448.bytesAt M p 10 = Spec.Ed448.bytesAt M p 4 ++
      (Spec.Ed448.bytesAt M (p + BitVec.ofNat 64 4) 4 ++ (Spec.Ed448.bytesAt M (p + BitVec.ofNat 64 8) 4).take 2) := by
    have a := Proof.X25519.bytesAt_add M p 4 6
    have b := Proof.X25519.bytesAt_add M (p + BitVec.ofNat 64 4) 4 2
    have b' := Proof.X25519.bytesAt_add M (p + BitVec.ofNat 64 8) 2 2
    have l := Proof.X25519.length_bytesAt M (p + BitVec.ofNat 64 8) 2
    rw [Offset.add_add] at b b'
    simp only [Proof.Ed448.bytesAt_eq]
    rw [a, show (6 : Nat) = 4 + 2 from rfl, b, show (4 : Nat) = 2 + 2 from rfl, b', List.take_left' l]
  rw [e10, bytes4, bytes4, bytes4, h0, h1, h2, hw]
  have e1 : Proof.X25519.leBytes 4 (0x45676953#32).toNat ++ Proof.X25519.leBytes 4 (0x38343464#32).toNat =
      "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) := by decide
  rw [← List.append_assoc, e1]
  refine congrArg (List.append _) ?_
  simp only [Proof.X25519.leBytes_succ, List.take_succ_cons, List.take_zero]
  have e2 : BitVec.ofNat 8 (c.toNat * 256) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, show (0 : BitVec 8).toNat = 0 from rfl]; omega
  have e3 : c.toNat * 256 / 256 = c.toNat := by omega
  rw [e2, e3]
  rfl

theorem hdr_len (c : BitVec 32) : (hdrBytes c).length = 10 := by simp [hdrBytes]

/-- The input of a hash, as the specification puts it together. -/
theorem dom4_eq (c : BitVec 32) (ctx x : List Byte) (hc : ctx.length = c.toNat) :
    Spec.Ed448.dom4 0 ctx ++ x = hdrBytes c ++ ctx ++ x := by
  simp [Spec.Ed448.dom4, hdrBytes, hc]

/-- `k` doublings of `eax`. -/
theorem dbl_ok {s : State} : ∀ k, WP isa (.block (List.replicate k (.alu .add .eax (.reg .eax)))) s fun u =>
    u.gpr .eax = BitVec.ofNat 32 (2 ^ k * (s.gpr .eax).toNat) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
      u.wr = s.wr ∧ ∀ r, r ≠ .eax → u.gpr r = s.gpr r
  | 0 => WP.block_nil ⟨by simp, rfl, rfl, rfl, fun _ _ => rfl⟩
  | k + 1 => by
    rw [List.replicate_succ', WP.block_append_iff]
    refine WP.mono (dbl_ok k) fun u ⟨h0, hm, hrd, hwr, ho⟩ => wp_add fun s' v _ => WP.block_nil
      ⟨?_, v.mem.trans hm, v.rd.trans hrd, v.wr.trans hwr, fun r hr => (v.other r hr).trans (ho r hr)⟩
    rw [v.gpr, h0, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, Nat.two_mul]

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem Kit.hdr_ok (hk : Kit E scr n ins outs) (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀)
    {j off : Nat} (hj : j < n) (hcl : (val j).toNat < 256) (ho : off + 12 ≤ 256) :
    WP isa (.block (hdrAt j off)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [fr E off 12] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (E.setWidth 64 + BitVec.ofNat 64 off) 10 = hdrBytes (val j) ∧
      ∀ r, r ≠ .eax → u.gpr r = t.gpr r := by
  have hf := hk.frame
  have ea : ∀ k ≤ 8, addr E (off + k) = E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 k := fun k hk' => by
    rw [addr_eq (by omega), Offset.add_add]
  have hw : ∀ k ≤ 8, InRegions t.wr (E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 k) 4 := fun k hk' => by
    rw [Offset.add_add]
    exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  have e0 : E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 0 = E.setWidth 64 + BitVec.ofNat 64 off :=
    BitVec.add_zero _
  unfold hdrAt
  rw [List.singleton_append, List.cons_append]
  refine wp_ldm (b := .esp) hc.esp (hk.readable hc j hj) fun s1 v1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok 8) fun s2 ⟨h2, m2, rd2, wr2, o2⟩ => ?_
  have esp2 : s2.gpr .esp = E := by rw [o2 _ (by decide), v1.other _ (by decide), hc.esp]
  have hwr2 : s2.wr = t.wr := by rw [wr2, v1.wr]
  refine wp_stm (b := .esp) (o := off + 8) esp2 (by rw [ea 8 (by omega), hwr2]; exact hw 8 (by omega))
    fun s3 v3 => wp_movi fun s4 v4 => ?_
  refine wp_stm (b := .esp) (o := off) (by rw [v4.other _ (by decide), v3.gpr, esp2])
    (by rw [v4.wr, v3.wr, hwr2, ← Nat.add_zero off, ea 0 (by omega)]; exact hw 0 (by omega))
    fun s5 v5 => wp_movi fun s6 v6 => ?_
  refine wp_stm (b := .esp) (o := off + 4)
    (by rw [v6.other _ (by decide), v5.gpr, v4.other _ (by decide), v3.gpr, esp2])
    (by rw [v6.wr, v5.wr, v4.wr, v3.wr, hwr2, ea 4 (by omega)]; exact hw 4 (by omega))
    fun u vu => WP.block_nil ?_
  have w0 : s2.gpr .eax = BitVec.ofNat 32 (2 ^ 8 * (val j).toNat) := by
    rw [h2, v1.gpr, hk.arg_word hc hj, ha j hj]
  have hm : u.mem = ((t.mem.writeW (E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 8)
      (BitVec.ofNat 32 (2 ^ 8 * (val j).toNat))).writeW
      (E.setWidth 64 + BitVec.ofNat 64 off) 0x45676953#32).writeW
      (E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 4) 0x38343464#32 := by
    rw [vu.mem, v6.gpr, v6.mem, v5.mem, v4.gpr, v4.mem, v3.mem, w0, m2, v1.mem, ea 8 (by omega), ea 4 (by omega),
      ← Nat.add_zero off, ea 0 (by omega), e0]
    rfl
  have hfr : Frame [fr E off 12] t.mem u.mem := by
    rw [hm]
    have c : ∀ k ≤ 8, (fr E off 12).Contains (E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 k) 4 :=
      fun k hk' => Offset.contains_base _ (by omega) (by omega)
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 8 (by omega))).writeW
      (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ (c 4 (by omega))
    have h := c 0 (by omega)
    rw [e0] at h
    exact h
  have gp : ∀ r, r ≠ .eax → u.gpr r = t.gpr r := fun r hr => by
    rw [vu.gpr, v6.other r hr, v5.gpr, v4.other r hr, v3.gpr, o2 r hr, v1.other r hr]
  refine ⟨?_, hfr, ?_, gp⟩
  · refine hc.of_frame (by rw [vu.rd, v6.rd, v5.rd, v4.rd, v3.rd, rd2, v1.rd])
      (by rw [vu.wr, v6.wr, v5.wr, v4.wr, v3.wr, hwr2]) (gp _ (by decide))
      (fun r hr _ => gp r (by rintro rfl; simp [calleeSaved] at hr)) hfr ?_
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ ho)
  · rw [hm]
    refine hdr_bytes _ _ _ _ ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega

end VG.Proof.Ed448.X86.Shake
