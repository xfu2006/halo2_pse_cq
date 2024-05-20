/** Utility functions.
Ported from IZPR Project
*/

use std::time::Instant;

pub const LOG2:usize = 0;
pub const LOG1:usize = 1;
pub const WARN:usize = 2;
pub const ERR:usize = 3;
pub const LOG_LEVEL:usize = LOG1;


/// timer class for recording time in microseconds
pub struct Timer{
	///running time in micro-second (accumulated)
	pub time_us: usize,

	// --- private data members --
	start_time: Instant,
}

/// timer class for recording time in microseconds
impl Timer{
	/// constructor
	pub fn new() -> Timer{
		return Timer{time_us: 0, start_time: Instant::now()};
	}

	/// start recording
	pub fn start(&mut self){
		self.start_time = Instant::now();
	}

	pub fn clear_start(&mut self){
		self.time_us = 0;
		self.start_time = Instant::now();
	}

	pub fn stop(&mut self){
		self.time_us += self.start_time.elapsed().as_micros() as usize;
	}

	pub fn clear(&mut self){
		self.time_us = 0;
	}
}

/// log function worker
pub fn log_worker(log_level: usize, msg: &String){
	if log_level>=LOG_LEVEL{
		println!("LOG: {}", msg);
	}
}

/// assuming it's DUMPING main node only
pub fn log(log_level: usize, msg: &String){
	log_worker(log_level, msg);
}

/// log theperformance print "log_title time_us"
pub fn log_perf(log_level: usize, log_title: &str, timer: &mut Timer){
	timer.stop();
	if timer.time_us<1000{
		log(log_level, &format!("{} {} us", log_title, timer.time_us));
	}else{
		log(log_level, &format!("{} {} ms", log_title, timer.time_us/1000));
	}
	timer.clear_start();
}

