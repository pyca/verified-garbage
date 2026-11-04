module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Impl.RsaPss.X86_64
public import VerifiedGarbage.Impl.MdHashTable.X86_64
public import VerifiedGarbage.Proof.MdHashTable.X86_64
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# RSASSA-PSS on x86-64: the calls through the tables' slots

`scall s ts` (`Impl/RsaPss/X86_64.lean`) runs as the call of the function
of `ts` whose address the slot `s` holds (`scall_ok`), when that function is
the first of `ts` at that address (as `TabOK` says of the tables of a
registration whose functions of distinct names are at distinct addresses).
`HT`: the slots of the table of `MdHash` hold the addresses of a hash
function's `init`, compression function and digest (`dn`), which the calls
of `MdFns` reach, in a view `W` of the frame's words; it holds of any view
that differs from `W` only in other words (`HT.upd`). `GT`: the slots of the
table of `Hash` hold the addresses of MGF1's hash function's streaming
functions, which the calls of `Fns` reach, and its digest length.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum (off word)

/-- The call of the function whose address the slot `s` (frame word `k`)
holds, `n`'s. -/
theorem scall_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {s k : Nat} (hk : s = 8 * k) (hkn : k < nW) (hs8 : s + 8 ≤ frameBytes) {n : String}
    {c : Prog isa} {ts : List (String × Prog isa)} (hw : W k = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Keep [.r11] t t' → t'.mem = t.mem → t'.syms = t.syms → WP isa (.call n c) t' Q) :
    WP isa (scall s ts) t Q := by
  refine WP.seq (WP.mono (WP.keep [.r11] (Q := fun t' => t'.gpr .r11 = t.syms n ∧ t'.mem = t.mem ∧
      t'.syms = t.syms) ?_ rfl) fun t' ⟨⟨h11, hm, hsy⟩, k⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := s) hs8, R.rd k hk hkn, hw, setReg_syms]
  · refine WP.icalls_of_call (a := t.syms n) (by simp only [icall, h11]) ?_ (h t' k hm hsy)
    show ts.find? (fun q => t'.syms q.1 == t.syms n) = _
    rw [hsy]; exact hf

theorem lay_keep11 {t t' : State} {F S : Addr} (L : Lay t F S) (k : Keep [.r11] t t') (hm : t'.mem = t.mem) :
    Lay t' F S := L.congr (k.gpr (by decide)) k.2.2 (by rw [hm])

theorem cs_keep11 {t t' : State} (k : Keep [.r11] t t') : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r :=
  fun r hr => k.gpr fun h => by simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)

theorem upd_ne' {α : Type} {f : Nat → α} {a x : Nat} (h : x ≠ a) (v : α) : upd f a v x = f x := by
  simp [upd, h]

/-- The slots of the table of `MdHash` (frame words 8, 9 and 10) hold the
addresses `sy` gives `H`'s `init`, compression function and digest (`dn`,
whose code is `digest H.P`), which the calls of `f` reach. -/
structure HT (H : Impl.Pbkdf2.Md.X86_64.Hash) (dn : String) (f : MdFns) (W : Nat → BitVec 64)
    (sy : String → Addr) : Prop where
  wi : W 8 = sy H.initN
  wc : W 9 = sy H.compN
  wd : W 10 = sy dn
  fi : f.init.find? (fun q => sy q.1 == sy H.initN) = some (H.initN, H.initC)
  fc : f.comp.find? (fun q => sy q.1 == sy H.compN) = some (H.compN, H.compC)
  fd : f.dig.find? (fun q => sy q.1 == sy dn) = some (dn, Impl.MdHashTable.X86_64.digest H.P)

/-- The calls of `f` reach `H`'s `init`, compression function and digest at
the addresses `sy` gives them: what `HT` says but for the slots. -/
structure HTF (H : Impl.Pbkdf2.Md.X86_64.Hash) (dn : String) (f : MdFns) (sy : String → Addr) : Prop where
  fi : f.init.find? (fun q => sy q.1 == sy H.initN) = some (H.initN, H.initC)
  fc : f.comp.find? (fun q => sy q.1 == sy H.compN) = some (H.compN, H.compC)
  fd : f.dig.find? (fun q => sy q.1 == sy dn) = some (dn, Impl.MdHashTable.X86_64.digest H.P)

theorem HTF.ht {H : Impl.Pbkdf2.Md.X86_64.Hash} {dn : String} {f : MdFns} {sy : String → Addr}
    (h : HTF H dn f sy) {W : Nat → BitVec 64} (h8 : W 8 = sy H.initN) (h9 : W 9 = sy H.compN)
    (h10 : W 10 = sy dn) : HT H dn f W sy :=
  ⟨h8, h9, h10, h.fi, h.fc, h.fd⟩

theorem HT.upd {H : Impl.Pbkdf2.Md.X86_64.Hash} {dn : String} {f : MdFns} {W : Nat → BitVec 64}
    {sy : String → Addr} (h : HT H dn f W sy) {k : Nat} (hk : k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10) (v : BitVec 64) :
    HT H dn f (upd W k v) sy :=
  ⟨(upd_ne' (Ne.symm hk.1) v).trans h.wi, (upd_ne' (Ne.symm hk.2.1) v).trans h.wc,
    (upd_ne' (Ne.symm hk.2.2) v).trans h.wd, h.fi, h.fc, h.fd⟩

theorem HT.congr {H : Impl.Pbkdf2.Md.X86_64.Hash} {dn : String} {f : MdFns} {W W' : Nat → BitVec 64}
    {sy sy' : String → Addr} (h : HT H dn f W sy) (hsy : sy' = sy) (h8 : W' 8 = W 8) (h9 : W' 9 = W 9)
    (h10 : W' 10 = W 10) : HT H dn f W' sy' := by
  subst hsy
  exact ⟨h8.trans h.wi, h9.trans h.wc, h10.trans h.wd, h.fi, h.fc, h.fd⟩

/-- The slots of the table of `Hash` (frame words 11 to 14) hold the
addresses `sy` gives `G`'s `init`, `update` and `finalize`, which the calls
of `g` reach, and its digest length. -/
structure GT (G : Impl.Pbkdf2.Md.X86_64.Stream) (g : Impl.Mgf1.X86_64.Table.Fns) (W : Nat → BitVec 64)
    (sy : String → Addr) : Prop where
  wi : W 11 = sy G.initN
  wu : W 12 = sy G.updN
  wf : W 13 = sy G.finN
  wd : W 14 = BitVec.ofNat 64 G.D
  fi : g.init.find? (fun q => sy q.1 == sy G.initN) = some (G.initN, G.initC)
  fu : g.upd.find? (fun q => sy q.1 == sy G.updN) = some (G.updN, G.updC)
  ff : g.fin.find? (fun q => sy q.1 == sy G.finN) = some (G.finN, G.finC)

/-- The calls of `g` reach `G`'s streaming functions at the addresses `sy`
gives them: what `GT` says but for the slots. -/
structure GTF (G : Impl.Pbkdf2.Md.X86_64.Stream) (g : Impl.Mgf1.X86_64.Table.Fns) (sy : String → Addr) : Prop where
  fi : g.init.find? (fun q => sy q.1 == sy G.initN) = some (G.initN, G.initC)
  fu : g.upd.find? (fun q => sy q.1 == sy G.updN) = some (G.updN, G.updC)
  ff : g.fin.find? (fun q => sy q.1 == sy G.finN) = some (G.finN, G.finC)

theorem GTF.gt {G : Impl.Pbkdf2.Md.X86_64.Stream} {g : Impl.Mgf1.X86_64.Table.Fns} {sy : String → Addr}
    (h : GTF G g sy) {W : Nat → BitVec 64} (h11 : W 11 = sy G.initN) (h12 : W 12 = sy G.updN)
    (h13 : W 13 = sy G.finN) (h14 : W 14 = BitVec.ofNat 64 G.D) : GT G g W sy :=
  ⟨h11, h12, h13, h14, h.fi, h.fu, h.ff⟩

theorem GT.congr {G : Impl.Pbkdf2.Md.X86_64.Stream} {g : Impl.Mgf1.X86_64.Table.Fns} {W W' : Nat → BitVec 64}
    {sy sy' : String → Addr} (h : GT G g W sy) (hsy : sy' = sy) (hW : ∀ k, 11 ≤ k → k ≤ 14 → W' k = W k) :
    GT G g W' sy' := by
  subst hsy
  exact ⟨(hW 11 (by decide) (by decide)).trans h.wi, (hW 12 (by decide) (by decide)).trans h.wu,
    (hW 13 (by decide) (by decide)).trans h.wf, (hW 14 (by decide) (by decide)).trans h.wd, h.fi, h.fu, h.ff⟩

/-- The tables `encode` and `checkEncoding` are given: the hash function
`H` of the table of `MdHash` (its digest `dn`), MGF1's `G` of the table of
`Hash`, and the functions the calls through their slots may reach (`f`,
`g`). -/
structure Tabs where
  H : Impl.Pbkdf2.Md.X86_64.Hash
  dn : String
  f : MdFns
  G : Impl.Pbkdf2.Md.X86_64.Stream
  g : Impl.Mgf1.X86_64.Table.Fns

/-- What `encode` and `checkEncoding` need of the tables at `pH` (of
`MdHash`) and `pG` (of `Hash`) in the state `s`: the words `hSlots` and
`gSlots` copy, the addresses of `H`'s and `G`'s functions and `G`'s digest
length, which the calls of `f` and `g` reach. -/
structure TabsAt (H : Impl.Pbkdf2.Md.X86_64.Hash) (dn : String) (f : MdFns) (G : Impl.Pbkdf2.Md.X86_64.Stream)
    (g : Impl.Mgf1.X86_64.Table.Fns) (pH pG : Addr) (s : State) : Prop where
  h0 : s.mem.readW (off pH 0) 64 = s.syms H.initN
  h3 : s.mem.readW (off pH 24) 64 = s.syms H.compN
  h4 : s.mem.readW (off pH 32) 64 = s.syms dn
  g0 : s.mem.readW (off pG 0) 64 = s.syms G.initN
  g1 : s.mem.readW (off pG 8) 64 = s.syms G.updN
  g2 : s.mem.readW (off pG 16) 64 = s.syms G.finN
  g4 : s.mem.readW (off pG 32) 64 = BitVec.ofNat 64 G.D
  hf : HTF H dn f s.syms
  gf : GTF G g s.syms

/-- The words of the tables that `hSlots` and `gSlots` copy, which two runs
agree on. -/
def tabWords (m : Mem) (pH pG : Addr) : List (BitVec 64) :=
  [m.readW (off pH 0) 64, m.readW (off pH 24) 64, m.readW (off pH 32) 64, m.readW (off pG 0) 64,
    m.readW (off pG 8) 64, m.readW (off pG 16) 64, m.readW (off pG 32) 64]

/-- What the calls of the digest of `H` need of its code, which the kernel
checks of each hash function: it never loads MXCSR or writes `rsp`, and
writes only `r8`, `r9`, `rbx`, `rbp` (which it restores) and `rax`, and it
is constant time. -/
structure DigOK (H : Impl.Pbkdf2.Md.X86_64.Hash) : Prop where
  mx : (Impl.MdHashTable.X86_64.digest H.P).allInstrs (fun i => !loadsMxcsr i) = true
  sp : NoSp (Impl.MdHashTable.X86_64.digest H.P)
  cl : ∀ r, r ∉ [Reg.r8, .r9, .rbx, .rbp, .rax] →
    ∀ i ∈ instrs (Impl.MdHashTable.X86_64.digest H.P), Taint.clobbers i r = false
  ct : ∀ md : MdStream.Md H.P.B H.P.N H.P.L, ConstantTime isa (Proof.MdHashTable.X86_64.digestK (P := H.P) md).pre
    (Proof.MdHashTable.X86_64.digestK (P := H.P) md).pub (Impl.MdHashTable.X86_64.digest H.P)

end VG.Proof.RsaPss.X86_64
