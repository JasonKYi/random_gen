import control.random

open io

/-! # Uniform generation -/

def random_num (n : ℕ) : io ℕ := 
io.rand 1 n

-- Given some seed, we generate a random number in `{1, ..., n}`.
#eval random_num 37 >>= print

def random_num_list' (n : ℕ) (m : ℕ) : list (io ℕ) :=
list.map (λ _, random_num n) (list.range m) 

def print_list_io {α : Type*} [has_to_string α] : list (io α) → io (list α)
| [] := return []
| (x :: xs) := do
  x' ← x,
  xs' ← print_list_io xs,
  return (x' :: xs')

-- Generate a list of random numbers uniformly in `{1, ..., n}` of size `m`.
def random_num_list (n : ℕ) (m : ℕ) : io (list ℕ) :=
print_list_io $ random_num_list' n m

#eval random_num_list 37 100 >>= print

/-! # Generation given some distribution -/

def normalize_distrib' : list ℕ → list ℕ 
| [] := []
| (x :: xs) := (list.sum (x :: xs)) :: normalize_distrib' xs

def normalize_distrib : list ℕ → list ℕ :=
list.reverse ∘ normalize_distrib' ∘ list.reverse

@[derive [decidable_pred]]
def list.placed (l : list ℕ) (n : ℕ) (i : ℕ) : Prop :=
if hi : i < l.length then n ≤ l.nth_le i hi else false

lemma lt_length_of_placed {l : list ℕ} {n : ℕ} {i : ℕ} (h : l.placed n i) : 
  i < l.length :=
begin
  rw [list.placed] at h,
  split_ifs at h with hi hi,
  exacts [hi, false.elim h],
end

lemma exists_placed_iff {l : list ℕ} {n : ℕ} : 
  (∃ i, l.placed n i) ↔ (∃ i, i < l.length ∧ l.placed n i) :=
⟨λ ⟨i, h⟩, ⟨i, lt_length_of_placed h, h⟩, λ ⟨i, _, h⟩, ⟨i, h⟩⟩

instance {l : list ℕ} {n : ℕ} : decidable (∃ i, l.placed n i) :=
decidable_of_iff' _ exists_placed_iff

def list.place (l : list ℕ) (n : ℕ) : ℕ :=
if hi : ∃ i, l.placed n i then @nat.find (l.placed n) infer_instance hi else l.length

def list.distribute (distrib : list ℕ) : 
  list ℕ → list ℕ
| [] := []
| (x :: xs) := distrib.place x :: list.distribute xs

def random_num_list_distrib (m : ℕ) (distrib : list ℕ) : io (list ℕ) := do 
  rnd ← random_num_list (list.sum distrib + 1) m,
  return ((normalize_distrib distrib).distribute rnd)
  
#eval random_num_list_distrib 100 [1, 1, 1, 1, 1, 1] >>= print

/-! # Historgram -/

def list.counts_occurence (l : list ℕ) : list ℕ :=
(list.range (l.foldr max 1 + 1)).map (λ n, l.count n)

def counts_occurence_io : io (list ℕ) → io (list ℕ) :=
functor.map list.counts_occurence

#eval counts_occurence_io (random_num_list_distrib 100 [1, 0, 0, 9, 8, 1]) >>= print