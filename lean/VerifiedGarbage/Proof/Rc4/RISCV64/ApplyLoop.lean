module

import VerifiedGarbage.Proof.Rc4.RISCV64.ApplyStep
public import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
public import VerifiedGarbage.Spec.Rc4

/-! # RC4 on RISC-V: the stream loop, on the table in the frame -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64) (h6 : s.gpr .t6 = 0#64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hp : InRegions s.wr (s.gpr .a7) 256) (hd : InRegions s.wr (s.gpr .a1) 1)
    (hs : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) 1) :
    let next := step { table := (contextAt s.mem (s.gpr .a7)).table, i, j }
    WP isa (.block applyStep) s fun t =>
      (contextAt t.mem (s.gpr .a7)).table = next.1.table ∧
      t.gpr .a3 = next.1.i.setWidth 64 ∧ t.gpr .t4 = next.1.j.setWidth 64 ∧
      t.mem (s.gpr .a1) = s.mem (s.gpr .a1) ^^^ next.2 ∧
      StreamFrame (s.gpr .a7) (s.gpr .a1) 1 s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .a7 = s.gpr .a7 ∧ t.gpr .t6 = s.gpr .t6 ∧
      t.gpr .a0 = s.gpr .a0 ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step s i j hcx h7 h6 hal hp hd) fun t ht => ?_
  obtain ⟨hmem, hrd, hwr, h0, h6', ha0, h1, h2, hi, hj⟩ := ht
  refine ⟨?_, hi, hj, ?_, ?_, hrd, hwr, h0, h6', ha0, h1, h2⟩
  · rw [hmem, table_write_sep _ _ _ _ hs, table_swap]
  · rw [hmem, write_byte, ite_eq_left rfl]
    have hne (idx : Byte) : s.gpr .a1 ≠ s.gpr .a7 + BitVec.ofNat 64 idx.toNat := by
      intro he
      have hn := hs (s.gpr .a1) (by rw [he, Mem.sub_ofNat_toNat _ (by omega)]; exact idx.isLt)
      exact hn (by simp [BitVec.sub_self])
    rw [write_byte, ite_eq_right (hne _), write_byte, ite_eq_right (hne _)]
    have ht := table_swap s.mem (s.gpr .a7) (i + 1#8)
      (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · rw [hmem]
    exact stream_frame_step _ _ _ _ _ _

/-- The unconsumed data remains unchanged by a stream iteration. -/
theorem apply_step_tail (s : State) (i j : Byte) (n : Nat)
    (hn : n + 1 < 2 ^ 64)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64) (h6 : s.gpr .t6 = 0#64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hp : InRegions s.wr (s.gpr .a7) 256) (hd : InRegions s.wr (s.gpr .a1) 1)
    (hs : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) (n + 1)) :
    WP isa (.block applyStep) s fun t =>
      bytesAt t.mem (s.gpr .a1 + 1#64) n = bytesAt s.mem (s.gpr .a1 + 1#64) n := by
  refine WP.mono (apply_step s i j hcx h7 h6 hal hp hd) fun t ht => ?_
  rw [ht.1]
  rw [bytes_write_sep _ _ _ _ _ (by omega)
    (sep_symm (Offset.sep_base (s.gpr .a1) (by decide) (by omega)))]
  exact bytes_table_frame _ _ _ _ _ (by omega) (swap_frame _ _ _ _)
    (sep_symm (sep_tail hn hs))

structure LoopPost (s : State) (ctx : Context) (n : Nat) (t : State) : Prop where
  table : (contextAt t.mem (s.gpr .a7)).table =
    (update ctx (bytesAt s.mem (s.gpr .a1) n)).1.table
  i : t.gpr .a3 = (update ctx (bytesAt s.mem (s.gpr .a1) n)).1.i.setWidth 64
  j : t.gpr .t4 = (update ctx (bytesAt s.mem (s.gpr .a1) n)).1.j.setWidth 64
  data : bytesAt t.mem (s.gpr .a1) n = (update ctx (bytesAt s.mem (s.gpr .a1) n)).2
  frame : StreamFrame (s.gpr .a7) (s.gpr .a1) n s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  p : t.gpr .a7 = s.gpr .a7
  zero : t.gpr .t6 = s.gpr .t6
  ctx : t.gpr .a0 = s.gpr .a0

/-- Streaming correctness by induction on the public byte count. -/
theorem apply_loop (n : Nat) (s : State) (ctx : Context)
    (hn : n + 1 < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .a7)).table = ctx.table)
    (hcx : s.gpr .a3 = ctx.i.setWidth 64) (h7 : s.gpr .t4 = ctx.j.setWidth 64)
    (h6 : s.gpr .t6 = 0#64) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hlen : s.gpr .a2 = BitVec.ofNat 64 (n + 1))
    (hp : InRegions s.wr (s.gpr .a7) 256)
    (hd : InRegions s.wr (s.gpr .a1) (n + 1))
    (hs : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) (n + 1)) :
    WP isa (.loop (.block applyStep) (.nonzero .a2)) s (LoopPost s ctx (n + 1)) := by
  induction n generalizing s ctx with
  | zero =>
    have hd1 : InRegions s.wr (s.gpr .a1) 1 := hd
    have hctx : ({ table := (contextAt s.mem (s.gpr .a7)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    have hstep := apply_step_table s ctx.i ctx.j hcx h7 h6 hal hp hd1 hs
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, h60, ha0, _, hcount⟩ := ht
    have hbytes (m : Mem) : bytesAt m (s.gpr .a1) 1 = [m (s.gpr .a1)] := by
      simp [bytesAt]
    refine ⟨_, t, .loopExit he ?_, ?_⟩
    · rw [Steps.eval_nonzero, hcount, hlen]
      rfl
    · constructor
      · simpa only [Nat.zero_add, hbytes, update] using htab
      · simpa only [Nat.zero_add, hbytes, update] using hti
      · simpa only [Nat.zero_add, hbytes, update] using htj
      · simp only [Nat.zero_add, hbytes, update, hbyte]
      · exact hf
      · exact hrd
      · exact hwr
      · exact hp0
      · exact h60
      · exact ha0
  | succ n ih =>
    have hd1 : InRegions s.wr (s.gpr .a1) 1 := by
      have hh := region_offset _ _ _ 0 1 (by decide) (by omega) hd
      simpa only [BitVec.add_zero] using hh
    have hs1 : Mem.Sep (s.gpr .a7) 256 (s.gpr .a1) 1 := fun x hx hy => hs x hx (by omega)
    have hctx : ({ table := (contextAt s.mem (s.gpr .a7)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    have hstep := apply_step_table s ctx.i ctx.j hcx h7 h6 hal hp hd1 hs1
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, ht6, ha0, hdptr, hcount⟩ := ht
    have htail : bytesAt t.mem (s.gpr .a1 + 1#64) (n + 1) =
        bytesAt s.mem (s.gpr .a1 + 1#64) (n + 1) := by
      obtain ⟨_, u, he', hh⟩ := apply_step_tail s ctx.i ctx.j (n + 1) hn hcx h7 h6 hal hp hd1 hs
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hh
    have htlen : t.gpr .a2 = BitVec.ofNat 64 (n + 1) := by
      rw [hcount, hlen]
      exact Offset.ofNat_sub_ofNat (by omega)
    have hpt : InRegions t.wr (t.gpr .a7) 256 := by rw [hwr, hp0]; exact hp
    have hdt : InRegions t.wr (t.gpr .a1) (n + 1) := by
      rw [hwr, hdptr]
      exact region_offset _ _ _ 1 (n + 1) (by decide) (by omega) hd
    have hst : Mem.Sep (t.gpr .a7) 256 (t.gpr .a1) (n + 1) := by
      rw [hp0, hdptr]
      exact sep_tail hn hs
    have htab' : (contextAt t.mem (t.gpr .a7)).table = (step ctx).1.table := by
      rw [hp0]; exact htab
    obtain ⟨tr', u, he', hu⟩ := ih t (step ctx).1 (by omega) htab' hti htj (ht6.trans h6)
      (by rw [hp0]; exact hal) htlen hpt hdt hst
    refine ⟨_, u, .loopNext he ?_ he', ?_⟩
    · rw [Steps.eval_nonzero, hcount, hlen, bne, len_ne n hn]
      rfl
    · have hresult : update ctx (bytesAt s.mem (s.gpr .a1) (n + 1 + 1)) =
          ((update (step ctx).1 (bytesAt t.mem (t.gpr .a1) (n + 1))).1,
            (s.mem (s.gpr .a1) ^^^ (step ctx).2) ::
              (update (step ctx).1 (bytesAt t.mem (t.gpr .a1) (n + 1))).2) := by
        rw [bytes_cons, hdptr, htail]
        rfl
      constructor
      · rw [hresult, ← hp0]; exact hu.table
      · rw [hresult]; exact hu.i
      · rw [hresult]; exact hu.j
      · rw [bytes_cons, hresult]
        have hh : u.mem (s.gpr .a1) = t.mem (s.gpr .a1) := by
          have hf' := hu.frame
          rw [hp0, hdptr] at hf'
          exact stream_head _ _ _ _ _ hn hf' hs
        rw [hh, hbyte, ← hdptr, hu.data]
      · have hf' := hu.frame
        rw [hp0, hdptr] at hf'
        exact stream_frame_trans_tail hf hf'
      · exact hu.rd.trans hrd
      · exact hu.wr.trans hwr
      · exact hu.p.trans hp0
      · exact hu.zero.trans ht6
      · exact hu.ctx.trans ha0

end VG.Proof.Rc4.RISCV64
