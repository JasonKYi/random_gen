import control.random

open io

/-! # Uniform generation -/

def random_fin (n : ℕ) (seed : ℕ) : io (fin n.succ) := 
io.run_rand_with seed (rand.random $ fin n.succ)

-- Given some seed, we generate a random number in `fin n.succ = {0, ..., n}`.
#eval random_fin 37 0 >>= print

-- Generate a list of random numbers in `fin n.succ` of size `m`.
def random_fin_list (n : ℕ) (m : ℕ) (seed : ℕ) : list (io $ fin n.succ) :=
list.map (random_fin n) (list.range' seed (m + seed)) 

def print_list_io {α : Type*} [has_to_string α] : list (io α) → io (list α)
| [] := return []
| (x :: xs) := do
  x' ← x,
  xs' ← print_list_io xs,
  return (x' :: xs')

#eval print_list_io (random_fin_list 37 3 0) >>= print

/-! # Generation given some distribution -/

