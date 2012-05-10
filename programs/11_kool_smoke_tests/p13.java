class c {
  void c() {  }
  void test() {
    System.out.print(-1);
    if (this instanceof c1) System.out.print(1);
    if (this instanceof c2) System.out.print(2);
    if (this instanceof c3) System.out.print(3);
  }
}

class c1 extends c {
  void c1() { super.c(); }
}

class c2 extends c {
  void c2() { super.c(); }
}

class c3 extends c {
  void c3() { super.c(); }
}

public class main {
  void main(String[] args) {
    (new c()).test();
    (new c1()).test();
    (new c2()).test();
    (new c3()).test();
  }
}

