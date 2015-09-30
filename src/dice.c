/*
 * dice.c
 *
 *  Created on: 3 de set de 2015
 *      Author: Arthur
 */

#include <stdlib.h>
#include "dice.h"

/* Creates a new dice with default configuration */
dice* new_dice(int diceIPos, int diceJPos){
	dice* n_dice = malloc(sizeof(dice));
	(*n_dice).bottom = 2;
	(*n_dice).front = 1;
	(*n_dice).right = 3;
	(*n_dice).i = diceIPos;
	(*n_dice).j = diceJPos;
	return n_dice;
}

/* Copy the values from d1 to d2*/
void copy_values(dice* d1, dice* d2){
	(*d2).bottom = (*d1).bottom;
	(*d2).front = (*d1).front;
	(*d2).right = (*d1).right;
}

/* The roll operations involves copy value from father dice to the son dice,
 * then, "roll" the die in place, updating its face values;
 */

int roll_up(dice* d, dice* pai){
	copy_values(pai, d);

	int old_top_side_value = 7 - (*d).bottom;
	(*d).bottom = (*d).front;
	(*d).front = old_top_side_value;
	return (*d).bottom;
}

int roll_right(dice* d, dice* pai){
	copy_values(pai, d);

	int old_top_side_value = 7 - (*d).bottom;
	(*d).bottom = (*d).right;
	(*d).right = old_top_side_value;
	return (*d).bottom;
}

int roll_down(dice* d, dice* pai){
	copy_values(pai, d);

	int old_down_side_value = 7 - (*d).front;
	(*d).front = (*d).bottom;
	(*d).bottom  = old_down_side_value;
	return (*d).bottom;
}

int roll_left(dice* d, dice* pai) {
	copy_values(pai, d);

	int old_left_side_value = 7 - (*d).right;
	(*d).right = (*d).bottom;
	(*d).bottom = old_left_side_value;
	return (*d).bottom;
}

int fake_roll_left(dice* d, dice* pai) {
	int old_left_side_value = 7 - (*d).right;
	return old_left_side_value;
}

int fake_roll_down(dice* d, dice* pai){
	int old_down_side_value = 7 - (*d).front;
	return old_down_side_value;
}

int fake_roll_right(dice* d, dice* pai){
	int old_top_side_value = 7 - (*d).bottom;
	return old_top_side_value;
}

int fake_roll_up(dice* d, dice* pai){
	int old_top_side_value = 7 - (*d).bottom;
	return old_top_side_value;
}
