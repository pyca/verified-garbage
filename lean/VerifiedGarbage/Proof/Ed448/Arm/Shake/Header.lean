import VerifiedGarbage.Impl.Ed448.Arm.Shake
import VerifiedGarbage.Proof.Ed448.Arm.Shake.Layout
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed448.Scalar

/-!
# Ed448 on ARMv7: the header of `dom4`

`Kit.hdr_ok`: the block `hdrAt j off` leaves `"SigEd448" ‖ 0 ‖ ctxlen`, the
first ten bytes of `dom4(0, context)`, in the frame at `off`, `ctxlen` the
saved word `j` (`hdr_bytes`: three little-endian words, the last
`ctxlen · 2^8`), and writes nothing else.
-/

namespace VG.Proof.Ed448.Arm.Shake

open VG VG.Arm VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Proof.X25519.Arm (Upd wp_mov wp_movw wp_str op2_lsl)
open VG.Proof.Ed25519.Arm (Whole.FR Whole.Ctx)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_addSp {d : Reg} {n : Nat} (hn : n < 256)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 32 n) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d n :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (by simp only [exec, hn, ite_true]) (k _ (Upd.setReg _ _ _))

theorem wp_ldrSp {r : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' r (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp r off :: is)) s Q := by
  subst ha
  exact VG.Proof.X25519.Arm.WP.cons (s' := s.setReg r (s.mem.readW _ 32))
    (by simp only [exec, ho, ite_true, State.load32, hin, Option.map_some]) (k _ (Upd.setReg _ _ _))

end

/-- `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (c : BitVec 32) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat]

theorem bytes4 (m : Mem) (p : Addr) : Spec.Ed448.bytesAt m p 4 = Proof.X25519.leBytes 4 (m.readW p 32).toNat := by
  rw [Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_leBytes]; simp [Mem.readW]

/-- The bytes of the three words of the header. -/
theorem hdr_bytes (m : Mem) (p : Addr) (c : BitVec 32) (hc : c.toNat < 256) :
    Spec.Ed448.bytesAt (((m.writeW (p + BitVec.ofNat 64 8) (c <<< 8)).writeW p 0x45676953#32).writeW
      (p + BitVec.ofNat 64 4) 0x38343464#32) p 10 =
      "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat] := by
  generalize hM : ((m.writeW (p + BitVec.ofNat 64 8) (c <<< 8)).writeW p 0x45676953#32).writeW
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
  have h2 : M.readW (p + BitVec.ofNat 64 8) 32 = c <<< 8 := by
    rw [← hM, Mem.readW_writeW_sep s84 (by decide), Mem.readW_writeW_sep s80 (by decide),
      Mem.readW_writeW_self32]
  have hw : (c <<< 8).toNat = c.toNat * 256 := by
    rw [VG.Proof.X25519.Arm.toNat_shl]; omega
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

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem Kit.hdr_ok (hk : Kit E scr n ins outs) (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀)
    {j off : Nat} (hj : Slot n j) (hcl : (val j).toNat < 256) (ho : off + 12 ≤ 248) :
    WP isa (.block (hdrAt j off)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨State.addr E + BitVec.ofNat 64 off, 12⟩] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr E + BitVec.ofNat 64 off) 10 = hdrBytes (val j) := by
  have hsp := hc.sp
  have ht := hk.top
  have hf := hk.fits
  have hjn := hj.1
  have hoff : (BitVec.ofNat 32 off).toNat = off := by rw [BitVec.toNat_ofNat]; omega
  have hEo : (E + BitVec.ofNat 32 off).toNat = E.toNat + off := by
    rw [BitVec.toNat_add_of_lt (by rw [hoff]; omega), hoff]
  have ea : ∀ k ≤ 8, State.addr (E + BitVec.ofNat 32 off + BitVec.ofNat 32 k) =
      State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 k := fun k hk => by
    rw [addr_add (by rw [hEo]; omega), addr_add (by omega)]
  have hw : ∀ k ≤ 8, InRegions t.wr (State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 k) 4 :=
    fun k hk => by
      rw [Offset.add_add]
      exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  have h256 : State.addr (t.sp + BitVec.ofNat 32 (248 + 4 * j)) = State.addr E + BitVec.ofNat 64 (248 + 4 * j) := by
    rw [hsp, addr_add (by omega)]
  obtain ⟨R, hR, hcon⟩ := hk.slot j hj
  have hin : InRegions (t.rd ++ t.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
    rw [hc.rd]; exact ⟨R, List.mem_append_left _ hR, hcon⟩
  have hv : t.mem.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 = val j := by
    rw [hk.arg_word hc hj, ha j hj]
  have e0 : State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 0 = State.addr E + BitVec.ofNat 64 off :=
    BitVec.add_zero _
  unfold hdrAt
  refine wp_ldrSp (by omega) h256 hin fun s1 v1 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s2 v2 => ?_
  refine wp_addSp (by omega) fun s3 v3 => ?_
  have r12 : ∀ s' : State, s'.gpr .r12 = s3.gpr .r12 → s'.gpr .r12 = E + BitVec.ofNat 32 off := fun s' h => by
    rw [h, v3.gpr, v2.sp, v1.sp, hsp]
  refine wp_str (a := State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 8) (by decide) (by rw [r12 s3 rfl]; exact ea 8 (by omega)) (by rw [v3.wr, v2.wr, v1.wr]; exact hw 8 (by omega))
    fun s4 v4 => ?_
  refine wp_movw fun s5 v5 => ?_
  refine wp_movt fun s6 v6 => ?_
  refine wp_str (a := State.addr E + BitVec.ofNat 64 off) (by decide) (by rw [r12 s6 (by rw [v6.other _ (by decide), v5.other _ (by decide), v4.gpr])]; exact (ea 0 (by omega)).trans e0)
    (by rw [v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr, ← e0]; exact hw 0 (by omega)) fun s7 v7 => ?_
  refine wp_movw fun s8 v8 => ?_
  refine wp_movt fun s9 v9 => ?_
  refine wp_str (a := State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 4) (by decide) (by
      rw [r12 s9 (by rw [v9.other _ (by decide), v8.other _ (by decide), v7.gpr, v6.other _ (by decide),
        v5.other _ (by decide), v4.gpr])]; exact ea 4 (by omega))
    (by rw [v9.wr, v8.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 4 (by omega)) fun u vu => ?_
  apply WP.block_nil
  have w0 : s2.gpr .r0 = val j <<< 8 := by rw [v2.gpr, v1.gpr, hv]
  have w1 : s6.gpr .r0 = 0x45676953#32 := by rw [v6.gpr, v5.gpr]; decide
  have w2 : s9.gpr .r0 = 0x38343464#32 := by rw [v9.gpr, v8.gpr]; decide
  have hm : u.mem = ((t.mem.writeW (State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 8) (val j <<< 8)).writeW
      (State.addr E + BitVec.ofNat 64 off) 0x45676953#32).writeW
      (State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 4) 0x38343464#32 := by
    rw [vu.mem, v9.mem, v8.mem, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem, w2, w1,
      v3.other _ (by decide), w0]
  have hfr : Frame [⟨State.addr E + BitVec.ofNat 64 off, 12⟩] t.mem u.mem := by
    rw [hm]
    have c : ∀ k ≤ 8, (⟨State.addr E + BitVec.ofNat 64 off, 12⟩ : Region).Contains
        (State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 k) 4 := fun k hk =>
      Offset.contains_base _ (by omega) (by omega)
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 8 (by omega))).writeW
      (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ (c 4 (by omega))
    have h := c 0 (by omega)
    rw [e0] at h
    exact h
  refine ⟨?_, hfr, by rw [hm]; exact hdr_bytes _ _ _ hcl⟩
  refine hc.of_frame (by rw [vu.rd, v9.rd, v8.rd, v7.rd, v6.rd, v5.rd, v4.rd, v3.rd, v2.rd, v1.rd])
    (by rw [vu.wr, v9.wr, v8.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr])
    (by rw [vu.sp, v9.sp, v8.sp, v7.sp, v6.sp, v5.sp, v4.sp, v3.sp, v2.sp, v1.sp]) ?_ hfr ?_
  · intro r hr _
    have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
    have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [vu.gpr, v9.other r h0, v8.other r h0, v7.gpr, v6.other r h0, v5.other r h0, v4.gpr,
      v3.other r h12, v2.other r h0, v1.other r h0]
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by omega))
end VG.Proof.Ed448.Arm.Shake
