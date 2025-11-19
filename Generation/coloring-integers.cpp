/*
   This program is generating different quadruples of numbers and checks if integers
   could be polychromaticly colored so that every shift of them contains at least 3 colors.

   It is used in paper
   Polychromatic Colorings on the Integers
   by
   Maria Axenovich, John Goldwasser, Bernard Lidicky, Ryan R. Martin, David Offner, John Talbot, Michael Young

   The program can be accelerated by using OpenMP. For gcc, it could be compiled using:
   g++ -O3 -fopenmp
   The program does not take any input.


   The program is running trough all patterns ABC = 0,a,b,c where c <= max_c_to_try = 288
   For each pattern ABC, the program tries to find a pattern P, such that tiling integers with
   PPPPPPP gives a 3-polychromatic coloring.

   Some patterns are obviously 3-polychromatic. For example is mod 3 of 0,a,b,c  gives all three classes 0,1,2
   the coloring 123123... is good. These things are tested in function is_interesting_pattern

   If a pattern is not obviously 3-polychromatic, we try all possible periods for P up to pattern_max_size
   and hope there will be a periodic coloring. The coloring is found using backtracking.

*/

#include <iostream>
#include <fstream>
#include <sstream>
#include <istream>
#include <vector>
#include <utility>
#include <assert.h>
#include <cstring>
#include <algorithm>
#include <cstdarg>
#include <cmath>
#include <limits>
#include <iomanip>


using namespace std;


const int max_c_to_try = 288; // how far do we go with c

// We try to find a periodic pattern for the coloring and
// we limit our search to patterns of length at most 1000.
// If none of length at most 1000 is found, we give up.
const int pattern_max_size = 30;



const int dstcnt = 4;  // number of distances, including 0  (patterns 0,a,b,c means dstcnt = 4)
const int colors = 3;  // number of colors to use


// Testing if patter in Z is polychromatic at position x
// Means it tests all copies of 0,a,b,c that contain x and if any is NOT 3-polychromatic, returns false
bool test(int x, int* Z, int period, int * distances)
{
  // shifting the pattern to match x to all of 0,a,b,c
  for (int shift = 0; shift < dstcnt; shift++)
  {

    // Counts how many times is each color present in the shifted 0,a,b,c
    int clrcnt[colors+1];
    for (int i = 0; i < colors+1; i++) clrcnt[i] = 0;

    for (int i = 0; i < dstcnt; i++)
    {
      int y = (x+distances[i]-distances[shift])%period;
      while (y < 0) y+= period;
      //cout << y << endl;
      clrcnt[Z[y]]++;
    }


    // Now we need to see at least three colors - that is counted by diff
    // However, color 0 means not colored yet, so it is added in the end as well.
    int diff = 0;
    for (int i = 1; i < colors+1; i++)
      if (clrcnt[i] > 0) diff++;
    diff += clrcnt[0];
    if (diff < colors) return false;
  }

  return true;
}

// Backtracking for filling pattern
// x .. Index in Z to color
// Z .. array with currently build pattern
// period .. desired final length of the pattern
// distances .. 0,a,b,c
bool color_next(int x, int* Z, int period, int * distances)
{
  if (x >= period)
  {
    return true;
  }

  for (int c = 1; c < colors+1; c++)
  {
    Z[x] = c;

    // Test if coloring Z[x] by c creates a copy of 0,a,b,c that is not 3-polychromatic
    if (!test(x,Z,period,distances)) continue;

    if (color_next(x+1,Z,period,distances)) return true;
  }
  Z[x] = 0;
  return false;
}


// We can eliminate some cases based on symmetries
// or existence of simple colorings or other obsevations, so we do not waste time with those
bool is_interesting_pattern(int *distances)
{
  int x = distances[1]-distances[0];
  int y = distances[2]-distances[1];
  int z = distances[3]-distances[2];

  // symmetry breaking
  // testing 0  3 4 5  is the same as 0 1 2 5 due to flip
  if (x > z) return false;

  // All three classes mod 3 -> coloring 123123...
  int mod3[] = {0,0,0};
  for (int i = 0; i < dstcnt; i++) mod3[distances[i]%3]++;
  if (mod3[0] > 0 &&  mod3[1] > 0 && mod3[2] > 0) return false;

  // Do not have a common divisor
  // Testing 0 3 6 27  can be reduced to testing 0 1 2 9
  for (int divisor = 2; divisor <= distances[1]; divisor++)
  {
    if (distances[1]%divisor == 0 &&  distances[2]%divisor == 0  && distances[3]%divisor == 0) return false;
  }

  // // Block coloring cases
  // // Means coloring like  1111 2222 3333 ..... will always work
  // if (x <= y && z <= y && y <= x+z) return false;
  // if (x <= z && y <= z && z <= x+y) return false;
  // if (y <= x && z <= x && x <= y+z) return false;

  return true;
}



int main(int argc, char *argv[])
{

  int max_period_found = 0;

  for (int c = 4; c <= max_c_to_try; c++)
  {
    int max_period_found_c = 0;
    for (int b = 2; b < c; b++)
    {
#pragma omp parallel for ordered schedule(dynamic)
      for (int a = 1; a < b; a++)
      {
        int Z[pattern_max_size];

        int  distances[dstcnt];
        distances[0] = 0;
        distances[1] = a;
        distances[2] = b;
        distances[3] = c;

        // Eliminate obviously 3-polychromatic patterns or patterns that are 3-poluchromatic iff some others are
        if (!is_interesting_pattern(distances)) continue;
        //cout << "Testing " << distances[0] << " " << distances[1] << " "  << distances[2] << " "  << distances[3] << endl;

        int period_found = -1;

        // Try if there is a polychromatic coloring of integers with period 'period'
        for (int period = 3; period < pattern_max_size; period++)
        {
          //cout << "Testing " << distances[0] << " " << distances[1] << " "  << distances[2] << " "  << distances[3] << "  for period " << period << endl;

          // Erase any previsou attempts
          for (int i = 0; i < period; i++) Z[i] = 0;

          // Without loss of generality we may assume that the pattern starts with 12
          Z[0] = 1;
          Z[1] = 2;

          // backtracking for finding the coloring
          if (color_next(2,Z,period,distances))
          {
            //cout << period << endl;
            //for (int i = 0; i < period; i++) cout << Z[i];
            // cout << endl;
            period_found = period;
            break;
          }
        }

#pragma omp ordered
        {
          cout << "0," << a << "," << b << "," << c << ";" << period_found << ";";
          for (int id = 0; id < period_found; id++)
          {
            cout << Z[id] << ",";
          }
          cout << endl;


          if (max_period_found < period_found)
          {
            max_period_found = period_found;
            //cout << "Got period " << period_found << " for (0," << a << "," << b << "," << c << ")" << endl;
          }
          if (max_period_found_c < period_found)
          {
            max_period_found_c = period_found;
          }
        }
      }
    }
    //cout << "c = " << c << " max_period_found_c was " << max_period_found_c << " total max is " <<  max_period_found << endl;
    cerr << "c = " << c << " max_period_found_c was " << max_period_found_c << " total max is " <<  max_period_found << endl;
  }

  // cout << "Done" << endl;


  return 0;
}
