/*
~
int b = 1; long a = 10;
~b : ~a
*/

public class exp_type_10_bit_neg {
  public static void main(String[] args) {
    int b = 1; long a = 10;

    System.out.println("f(true  ? ~b : ~a): " + f(true  ? ~b : ~a));
    System.out.println("f(false ? ~b : ~a): " + f(false ? ~b : ~a));

    System.out.println("Done!");
  }

  static String f(int b) {
    return "f(int): " + b;
  }

  static String f(long a) {
    return "f(long): " + a;
  }
}
