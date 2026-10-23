module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.ApplyStep
public import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc4.Table

/-! # RC4 on PPC64LE: the stream function -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Spec.Rc4 VG.Proof.Rc4

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h7 : s.gpr .r7 = j.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hp : InRegions s.wr (s.gpr .r3) 256) (hd : InRegions s.wr (s.gpr .r4) 1)
    (hs : Mem.Sep (s.gpr .r3) 256 (s.gpr .r4) 1) :
    let next := step { table := (contextAt s.mem (s.gpr .r3)).table, i, j }
    WP isa (.block applyStep) s fun t =>
      (contextAt t.mem (s.gpr .r3)).table = next.1.table ∧
      t.gpr .r6 = next.1.i.setWidth 64 ∧ t.gpr .r7 = next.1.j.setWidth 64 ∧
      t.mem (s.gpr .r4) = s.mem (s.gpr .r4) ^^^ next.2 ∧
      StreamFrame (s.gpr .r3) (s.gpr .r4) 1 s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r8 = s.gpr .r8 ∧
      t.gpr .r4 = s.gpr .r4 + 1#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64 := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step s i j hcx h7 h8 hp hd) fun t ht => ?_
  obtain ⟨hmem, hrd, hwr, h0, h8', h1, h2, hi, hj⟩ := ht
  refine ⟨?_, hi, hj, ?_, ?_, hrd, hwr, h0, h8', h1, h2⟩
  · rw [hmem, table_write_sep _ _ _ _ hs, table_swap]
  · rw [hmem, write_byte, ite_eq_left rfl]
    have hne (idx : Byte) : s.gpr .r4 ≠ s.gpr .r3 + BitVec.ofNat 64 idx.toNat := by
      intro he
      have hn := hs (s.gpr .r4) (by rw [he, Mem.sub_ofNat_toNat _ (by omega)]; exact idx.isLt)
      exact hn (by simp [BitVec.sub_self])
    rw [write_byte, ite_eq_right (hne _), write_byte, ite_eq_right (hne _)]
    have ht := table_swap s.mem (s.gpr .r3) (i + 1#8)
      (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · rw [hmem]
    exact stream_frame_step _ _ _ _ _ _

/-- The unconsumed data remains unchanged by a stream iteration. -/
theorem apply_step_tail (s : State) (i j : Byte) (n : Nat)
    (hn : n + 1 < 2 ^ 64)
    (hcx : s.gpr .r6 = i.setWidth 64) (h7 : s.gpr .r7 = j.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hp : InRegions s.wr (s.gpr .r3) 256) (hd : InRegions s.wr (s.gpr .r4) 1)
    (hs : Mem.Sep (s.gpr .r3) 256 (s.gpr .r4) (n + 1)) :
    WP isa (.block applyStep) s fun t =>
      bytesAt t.mem (s.gpr .r4 + 1#64) n = bytesAt s.mem (s.gpr .r4 + 1#64) n := by
  refine WP.mono (apply_step s i j hcx h7 h8 hp hd) fun t ht => ?_
  rw [ht.1]
  rw [bytes_write_sep _ _ _ _ _ (by omega)
    (sep_symm (Offset.sep_base (s.gpr .r4) (by decide) (by omega)))]
  exact bytes_table_frame _ _ _ _ _ (by omega) (swap_frame _ _ _ _)
    (sep_symm (sep_tail hn hs))

structure LoopPost (s : State) (ctx : Context) (n : Nat) (t : State) : Prop where
  table : (contextAt t.mem (s.gpr .r3)).table =
    (update ctx (bytesAt s.mem (s.gpr .r4) n)).1.table
  i : t.gpr .r6 = (update ctx (bytesAt s.mem (s.gpr .r4) n)).1.i.setWidth 64
  j : t.gpr .r7 = (update ctx (bytesAt s.mem (s.gpr .r4) n)).1.j.setWidth 64
  data : bytesAt t.mem (s.gpr .r4) n = (update ctx (bytesAt s.mem (s.gpr .r4) n)).2
  frame : StreamFrame (s.gpr .r3) (s.gpr .r4) n s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  p : t.gpr .r3 = s.gpr .r3

theorem len_ne (n : Nat) (hn : n + 1 + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (n + 1 + 1) - 1#64 == (0 : BitVec 64)) = false := by
  apply beq_eq_false_iff_ne.mpr
  rw [Offset.ofNat_sub_ofNat (by omega)]
  intro hz0
  have hh := congrArg BitVec.toNat hz0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hh
  change n + 1 + 1 - 1 = 0 at hh
  omega

/-- Streaming correctness by induction on the public byte count. -/
theorem apply_loop (n : Nat) (s : State) (ctx : Context)
    (hn : n + 1 < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .r3)).table = ctx.table)
    (hcx : s.gpr .r6 = ctx.i.setWidth 64) (h7 : s.gpr .r7 = ctx.j.setWidth 64)
    (h8 : s.gpr .r8 = 0)
    (hlen : s.gpr .r5 = BitVec.ofNat 64 (n + 1))
    (hp : InRegions s.wr (s.gpr .r3) 256)
    (hd : InRegions s.wr (s.gpr .r4) (n + 1))
    (hs : Mem.Sep (s.gpr .r3) 256 (s.gpr .r4) (n + 1)) :
    WP isa (.loop (.block applyStep) (.nonzero .d .r5)) s (LoopPost s ctx (n + 1)) := by
  induction n generalizing s ctx with
  | zero =>
    have hd1 : InRegions s.wr (s.gpr .r4) 1 := hd
    have hctx : ({ table := (contextAt s.mem (s.gpr .r3)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    have hstep := apply_step_table s ctx.i ctx.j hcx h7 h8 hp hd1 hs
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, _, _, hcount⟩ := ht
    have hbytes (m : Mem) : bytesAt m (s.gpr .r4) 1 = [m (s.gpr .r4)] := by
      simp [bytesAt]
    refine ⟨_, t, .loopExit he ?_, ?_⟩
    · simp only [eval, State.read, BitVec.setWidth_eq, hcount, hlen]
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
  | succ n ih =>
    have hd1 : InRegions s.wr (s.gpr .r4) 1 := by
      have hh := region_offset _ _ _ 0 1 (by decide) (by omega) hd
      simpa only [BitVec.add_zero] using hh
    have hs1 : Mem.Sep (s.gpr .r3) 256 (s.gpr .r4) 1 := fun x hx hy => hs x hx (by omega)
    have hctx : ({ table := (contextAt s.mem (s.gpr .r3)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    have hstep := apply_step_table s ctx.i ctx.j hcx h7 h8 hp hd1 hs1
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, ht8, hdptr, hcount⟩ := ht
    have htail : bytesAt t.mem (s.gpr .r4 + 1#64) (n + 1) =
        bytesAt s.mem (s.gpr .r4 + 1#64) (n + 1) := by
      obtain ⟨_, u, he', hh⟩ := apply_step_tail s ctx.i ctx.j (n + 1) hn hcx h7 h8 hp hd1 hs
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hh
    have htlen : t.gpr .r5 = BitVec.ofNat 64 (n + 1) := by
      rw [hcount, hlen]
      exact Offset.ofNat_sub_ofNat (by omega)
    have hpt : InRegions t.wr (t.gpr .r3) 256 := by rw [hwr, hp0]; exact hp
    have hdt : InRegions t.wr (t.gpr .r4) (n + 1) := by
      rw [hwr, hdptr]
      exact region_offset _ _ _ 1 (n + 1) (by decide) (by omega) hd
    have hst : Mem.Sep (t.gpr .r3) 256 (t.gpr .r4) (n + 1) := by
      rw [hp0, hdptr]
      exact sep_tail hn hs
    have htab' : (contextAt t.mem (t.gpr .r3)).table = (step ctx).1.table := by
      rw [hp0]; exact htab
    obtain ⟨tr', u, he', hu⟩ := ih t (step ctx).1 (by omega) htab' hti htj (ht8.trans h8) htlen
      hpt hdt hst
    refine ⟨_, u, .loopNext he ?_ he', ?_⟩
    · simp only [eval, State.read, BitVec.setWidth_eq, hcount, hlen, bne, len_ne n hn,
        Bool.not_false]
    · have hresult : update ctx (bytesAt s.mem (s.gpr .r4) (n + 1 + 1)) =
          ((update (step ctx).1 (bytesAt t.mem (t.gpr .r4) (n + 1))).1,
            (s.mem (s.gpr .r4) ^^^ (step ctx).2) ::
              (update (step ctx).1 (bytesAt t.mem (t.gpr .r4) (n + 1))).2) := by
        rw [bytes_cons, hdptr, htail]
        rfl
      constructor
      · rw [hresult, ← hp0]; exact hu.table
      · rw [hresult]; exact hu.i
      · rw [hresult]; exact hu.j
      · rw [bytes_cons, hresult]
        have hh : u.mem (s.gpr .r4) = t.mem (s.gpr .r4) := by
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

theorem apply_finish (s : State) (ctx : Context) (d : Addr) (n : Nat) (hn : n < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .r3)).table = ctx.table)
    (hcx : s.gpr .r6 = ctx.i.setWidth 64) (h7 : s.gpr .r7 = ctx.j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .r3) 258)
    (hs : Mem.Sep d n (s.gpr .r3) 258) :
    WP isa (.block [.stb .r6 .r3 256, .stb .r7 .r3 257]) s fun t =>
      contextAt t.mem (s.gpr .r3) = ctx ∧ bytesAt t.mem d n = bytesAt s.mem d n ∧
      t.mem = (s.mem.write (s.gpr .r3 + 256#64) 1 ctx.i).write (s.gpr .r3 + 257#64) 1 ctx.j := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, hcx, h7, low_byte]
  refine ⟨?_, ?_⟩
  · rw [context_finish, htable]
  · rw [bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide)),
      bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide))]

theorem apply_start (s : State) (hp : InRegions (s.rd ++ s.wr) (s.gpr .r3) 258) :
    WP isa (.block [.lbz .r6 .r3 256, .lbz .r7 .r3 257, .li .r8 0]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = s.gpr .r5 ∧
      t.gpr .r6 = (contextAt s.mem (s.gpr .r3)).i.setWidth 64 ∧
      t.gpr .r7 = (contextAt s.mem (s.gpr .r3)).j.setWidth 64 ∧ t.gpr .r8 = 0 := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, contextAt]

/-- Memory changed only within the context and the data. -/
def ApplyFrame (p d : Addr) (n : Nat) (m m' : Mem) : Prop :=
  ∀ x, ¬ (x - p).toNat < 258 → ¬ (x - d).toNat < n → m' x = m x

theorem apply_ok (s : State)
    (hp : InRegions s.wr (s.gpr .r3) 258)
    (hd : InRegions s.wr (s.gpr .r4) (s.gpr .r5).toNat)
    (hs : Mem.Sep (s.gpr .r3) 258 (s.gpr .r4) (s.gpr .r5).toNat) :
    WP isa VG.Impl.Rc4.PPC64LE.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .r3))
        (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
      (contextAt t.mem (s.gpr .r3) = result.1 ∧
        bytesAt t.mem (s.gpr .r4) (s.gpr .r5).toNat = result.2) ∧
      ApplyFrame (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat s.mem t.mem := by
  have hpRead : InRegions (s.rd ++ s.wr) (s.gpr .r3) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold VG.Impl.Rc4.PPC64LE.apply
  refine WP.seq (WP.mono (apply_start s hpRead) fun a ha => ?_)
  obtain ⟨ham, har, haw, ha0, ha1, ha2, ha6, ha7, ha8⟩ := ha
  refine WP.ite (s.gpr .r5 == 0) (by simp only [eval, State.read, BitVec.setWidth_eq, ha2])
    (fun hz => ?_) (fun hnz => ?_)
  · have hz' : s.gpr .r5 = 0 := beq_iff_eq.mp hz
    refine WP.block_nil ?_
    simp only [hz', ham]
    exact ⟨⟨context_ext rfl rfl rfl, rfl⟩, fun _ _ _ => rfl⟩
  · have hnz' : s.gpr .r5 ≠ 0 := beq_eq_false_iff_ne.mp hnz
    obtain ⟨n, hnEq⟩ := Nat.exists_eq_succ_of_ne_zero (show (s.gpr .r5).toNat ≠ 0 by
      intro h; exact hnz' (BitVec.eq_of_toNat_eq h))
    change (s.gpr .r5).toNat = n + 1 at hnEq
    have hbound : n + 1 < 2 ^ 64 := by rw [← hnEq]; exact (s.gpr .r5).isLt
    have hpa : InRegions a.wr (a.gpr .r3) 256 := by
      rw [haw, ha0]
      have hh := region_offset _ _ _ 0 256 (by decide) (by decide) hp
      simpa only [BitVec.add_zero] using hh
    have hda : InRegions a.wr (a.gpr .r4) (n + 1) := by rw [haw, ha1, ← hnEq]; exact hd
    have hsa : Mem.Sep (a.gpr .r3) 256 (a.gpr .r4) (n + 1) := by
      rw [ha0, ha1, ← hnEq]
      exact fun x hx hy => hs x (by omega) hy
    have htable : (contextAt a.mem (a.gpr .r3)).table = (contextAt s.mem (s.gpr .r3)).table := by
      rw [ham, ha0]
    have hlen : a.gpr .r5 = BitVec.ofNat 64 (n + 1) := by
      rw [ha2, ← hnEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.seq (WP.mono (apply_loop n a (contextAt s.mem (s.gpr .r3)) hbound htable ha6 ha7
      ha8 hlen hpa hda hsa) fun b hb => ?_)
    have hpb : InRegions b.wr (b.gpr .r3) 258 := by rw [hb.wr, hb.p, haw, ha0]; exact hp
    have hsb : Mem.Sep (s.gpr .r4) (n + 1) (b.gpr .r3) 258 := by
      rw [hb.p, ha0, ← hnEq]
      exact sep_symm hs
    have htab : (contextAt b.mem (b.gpr .r3)).table =
        (update (contextAt s.mem (s.gpr .r3)) (bytesAt a.mem (a.gpr .r4) (n + 1))).1.table := by
      rw [hb.p]; exact hb.table
    refine WP.mono (apply_finish b _ (s.gpr .r4) (n + 1) (by omega) htab hb.i hb.j hpb hsb)
      fun t ⟨htc, htd, htm⟩ => ?_
    have hdata := hb.data
    rw [ha1, ham] at hdata
    rw [hb.p, ha0, ham, ha1] at htc
    rw [hnEq]
    refine ⟨⟨htc, htd.trans hdata⟩, ?_⟩
    intro x hx hy
    have hf := hb.frame
    rw [ha0, ha1, ham] at hf
    rw [htm, hb.p, ha0]
    have h1 : x ≠ s.gpr .r3 + 256#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    have h2 : x ≠ s.gpr .r3 + 257#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    rw [write_byte, ite_eq_right h2, write_byte, ite_eq_right h1]
    exact hf x (by omega) hy

end VG.Proof.Rc4.PPC64LE
