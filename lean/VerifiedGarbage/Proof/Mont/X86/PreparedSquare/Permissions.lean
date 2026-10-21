module

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Timing
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint

/-! # Read-only cached geometry and the caller's wider permissions -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Args.withRegions {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (h : Args s W L A) {rd wr : List Region}
    (covered : Covers (s.rd ++ s.wr) (rd ++ wr)) : Args (s.withRegions rd wr) W L A :=
  ⟨fun i hi => readSrc_widen covered (h.read i hi), h.far, h.inverse, h.modulus⟩

theorem Args.word {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (h : Args s W L A) {i : Nat} (hi : i ∈ [0, 2, 3, 7]) :
    s.mem.readW (s.ea (cacheArg i)) 32 = cacheValue A i := by
  have H := h.read i hi
  change s.load32 (s.ea (cacheArg i)) = some (cacheValue A i) at H
  unfold State.load32 at H
  split at H
  · exact Option.some.inj H
  · cases H

theorem Args.publicWords {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (S : Args s W L A) (T : Args t W L A) : ∀ i < 3, arg s i = arg t i := by
  intro i hi
  match i, hi with
  | 0, _ =>
    change s.mem.readW (s.ea (cacheArg 3)) 32 = t.mem.readW (t.ea (cacheArg 3)) 32
    exact (S.word (by decide : 3 ∈ [0, 2, 3, 7])).trans (T.word (by decide)).symm
  | 1, _ =>
    change s.mem.readW (s.ea (cacheArg 7)) 32 = t.mem.readW (t.ea (cacheArg 7)) 32
    exact (S.word (by decide : 7 ∈ [0, 2, 3, 7])).trans (T.word (by decide)).symm
  | 2, _ =>
    change s.mem.readW (s.ea (cacheArg 2)) 32 = t.mem.readW (t.ea (cacheArg 2)) 32
    exact (S.word (by decide : 2 ∈ [0, 2, 3, 7])).trans (T.word (by decide)).symm

theorem cached_agree {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (S : Args s W L A) (T : Args t W L A)
    (sp : s.gpr .esp = t.gpr .esp) (scratch : s.gpr .edi = t.gpr .edi)
    (sout : ArgsOut 3 s) (tout : ArgsOut 3 t) : VG.X86.Taint.Agree columnTaint s t := by
  exact agree_argTaint (rs := [.edi]) (k := 3)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact scratch)
    sp sout tout (S.publicWords T)

theorem trace_narrow_of_wp {c : Prog isa} {s t : State} {rd wr : List Region} {Q : State → Prop}
    (H : WP isa c (s.withRegions rd wr) Q)
    (read : Covers (rd ++ wr) (s.rd ++ s.wr)) (write : Covers wr s.wr)
    {tr : List Leak} (E : Exec isa c s tr t) :
    ∃ u, Exec isa c (s.withRegions rd wr) tr u := by
  obtain ⟨tr', u, EU, _⟩ := H
  have EW := VG.X86.Exec.widen EU read write
  simp only [State.withRegions_withRegions, State.withRegions_self] at EW
  obtain ⟨rfl, _⟩ := Exec.det E EW
  exact ⟨u, EU⟩

theorem columns_trace_of_readonly {s t u v : State} {sr sw tr tw : List Region}
    {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (S : Args (s.withRegions sr sw) W L A) (T : Args (t.withRegions tr tw) W L A)
    (sp : s.gpr .esp = t.gpr .esp) (scratch : s.gpr .edi = t.gpr .edi)
    (sout : ArgsOut 3 (s.withRegions sr sw)) (tout : ArgsOut 3 (t.withRegions tr tw))
    (srun : WP isa VG.Impl.Mont.X86.PreparedSquare.columns (s.withRegions sr sw) fun _ => True)
    (trun : WP isa VG.Impl.Mont.X86.PreparedSquare.columns (t.withRegions tr tw) fun _ => True)
    (sread : Covers (sr ++ sw) (s.rd ++ s.wr)) (swrite : Covers sw s.wr)
    (tread : Covers (tr ++ tw) (t.rd ++ t.wr)) (twrite : Covers tw t.wr)
    {ls lt : List Leak} (ES : Exec isa VG.Impl.Mont.X86.PreparedSquare.columns s ls u)
    (ET : Exec isa VG.Impl.Mont.X86.PreparedSquare.columns t lt v) : ls = lt := by
  obtain ⟨u', EU⟩ := trace_narrow_of_wp srun sread swrite ES
  obtain ⟨v', EV⟩ := trace_narrow_of_wp trun tread twrite ET
  exact columns_constantTime _ _ _ _ _ _ True.intro True.intro
    (cached_agree S T sp scratch sout tout) EU EV

end VG.Proof.Mont.X86.PreparedSquare
