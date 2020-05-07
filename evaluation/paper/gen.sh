#!/bin/sh

for n in {5..50..5}
do
    r="[env_vars]
pending
src_floor     : [0..$n]
dest_floor    : [0..$n]
current_floor : [0..$n]

[sys_vars]
move          : [0..2]

[env_trans]
!pending & pending'                     -> src_floor' = current_floor'
pending                                 -> (src_floor' = src_floor & dest_floor' = dest_floor)
pending & !(current_floor = dest_floor) -> pending'
(current_floor = dest_floor) & pending  -> !pending'
move = 2 & current_floor < $n   -> current_floor' = current_floor + 1
move = 1                                -> current_floor' = current_floor
move = 0 & current_floor > 0            -> current_floor' = current_floor - 1

[sys_trans]
current_floor = $n  -> !(move = 2)
current_floor = 0           -> !(move = 0)

[weights]
pending & !(current_floor = dest_floor) : -1
"
    for i in $(seq 1 $n)
    do
        r+="pending & !pending' & (src_floor - dest_floor) = $i | (dest_floor - src_floor) = $i : $i
"
    done
    echo "$r" > ./evaluation/paper/generated_specs/lift_$n
done
