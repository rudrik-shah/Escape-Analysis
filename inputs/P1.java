class Example extends Thread{
	 Example field;
	 static Example sfield;
	
	 public static void main(String args[]) {
		
		 Example obj1, obj2;
		
		 obj1 = new Example();				// O1
		 
		 obj1.start();
		 obj1.foo();
		 
		 obj1.join();
		 
		 obj2 = obj1.field;
	 }
	
	 public void run() {
		 this.field = new Example();		// O2
		 sfield = this; 
	 }
	 
	 void foo() {
		 this.field = new Example();		// O3
		 sfield = new Exapmle();			// O4
	 }
}



