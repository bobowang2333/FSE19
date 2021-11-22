/*
 * Author: Markus Kusano
 *
 * A class of static utility functions 
 */
#pragma once

#include <string>

struct Utils {
  // Return a SMT-LIB2 const bitvector form of the passed unsigned
  static std::string to_const_bitvec(unsigned i);
};
