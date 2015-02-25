import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.text.SimpleDateFormat;
import java.util.Calendar;

public class JMLsample1 {	
	public static double radius,pilength;
	
	/*@ requires radius>=0;
	  @ ensures radius>= 0;
	  @ ensures pilength > 0 && pilength <=3.14;
	  @*/
	public static void main(String[] args)
	{		
		BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
		System.out.println("\nCIRCLE AND TIMER APPLICATION-MULTI-THREADING");
		System.out.println("---------------------------------------------");
		try {
			System.out.print("Enter radius: ");
			radius = Double.parseDouble(br.readLine());
			System.out.print("Enter pi: ");
			pilength=Double.parseDouble(br.readLine());
		} catch (NumberFormatException | IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		AreaThread a1 = new AreaThread(radius,pilength);
		a1.start();
		a1.run();
		a1.display();
		CircumThread a2 = new CircumThread(radius,pilength);
		a2.start();
		a2.run();
		a2.display();
		Timer t1 = new Timer();
		t1.start();
		    }
	} 
    
class AreaThread extends Thread {
	double radius_thread, pi_thread,area;
	/*@ requires radius>=0;
	  @ ensures radius>= 0;
	  @ ensures pi > 0 && pi <=3.14;
	  @*/
	AreaThread(double radius,double pi)
	{
		  radius_thread=radius;
		  pi_thread=pi;
		
	}
	/*@ requires pi_thread<=3.14 && pi_thread>=0
          @ requires radius_thread>=0
          @ ensures area >=0;
	  @*/
    public void run() {   	
     area=pi_thread * radius_thread * radius_thread;    	
    }
	/*@ invariant area<0; 
	  @*/
    public void display()
    {
    	System.out.println("Area : "+ area);

    }
}

class CircumThread extends Thread {
	double radius_thread, pi_thread,circum;
	/*@ requires radius>=0;
	  @ ensures radius_thread>= 0;
	  @ ensures pi_thread > 0 && pi_thread <=3.14;
	  @*/
	CircumThread(double radius,double pi)
	{
		  radius_thread=radius;
		  pi_thread=pi;		
	}
	/*@ requires radius_thread>= 0;
	  @ requires pi_thread > 0 && pi_thread <=3.14;
	  @ ensures circum>=0;
	  @*/
    public void run() {   	
    	circum=2*pi_thread * radius_thread;    	
    }
	/*@ invariant circum >=0;
	  @*/
    public void display()
    {   
     	System.out.println("Circumference :" + circum);
    }
}

class Timer extends Thread
{
	String timeStamp;
	/*@ ensures timeStamp!=null;
	  @*/
	public void run()
	{
	timeStamp = new SimpleDateFormat("HH:mm:ss").format(Calendar.getInstance().getTime());
	System.out.println("US time:" + timeStamp);
	IndiaTime ind1=new IndiaTime(timeStamp);	
	ind1.start();
	
	}
}

class IndiaTime extends Thread
{  String current_time=new String();
   int h,m;
	/*@ ensures current_time!=null;
	  @*/
	IndiaTime(String nowTime)
	{
		current_time=nowTime;
	}
	/*@ requires current_time!=null;
	  @ ensures h>= 0 && h<24;
	  @ ensures m>0 && m<60;
	  @ ensures current_time == \old(current_time);
	  @*/
	public void run()
	{
			String[] split1 =current_time.split(":");
			
		       h=Integer.parseInt(split1[0])+10;
			if (h>=24)
			{
				h=h-24;
			}
			
			m=Integer.parseInt(split1[1])+30;
			if(m>=60)
			{
				h=h+1;
				m=m-60;
			}
			current_time=String.valueOf(h)+":"+String.valueOf(m)+":"+split1[2];
			System.out.print("India Time : " );
			System.out.println(current_time);			
	}
}



