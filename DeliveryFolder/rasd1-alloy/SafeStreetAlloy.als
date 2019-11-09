open util/time
open util/integer

sig Str{}

--Account
abstract sig User{
	username: one Str,
	password: one Str,
	email: one Str,
	seeGroupedStatistics: lone GroupedStatistics
}

sig EndUser extends User{
	name: one Str,
	surname: one Str
}

sig Authority extends User{
	CUU: one Str,
	name: one Str,
	seeCityStatistic: lone CityStatistic
}

sig Image{
	capturedlLicenseplate: lone Licenseplate
}

sig Report{
	user: one EndUser,
	position: one Street,
	violation: one ViolationEnum,
  	picture: one Image,
	licenseplateHelper: lone Licenseplate,
	datetime: one Time
}

sig Vehicle{
	vehicleplate: one Licenseplate,
	type: one Str
}

sig Licenseplate{}

sig Street{
	name: one Str,
	city: one City
}

sig City{
	cityName: one Str
}

sig CityStatistic{
	relatedCity: one City,
	fromCityReports: set Report
}

lone sig GroupedStatistics{
	fromReports: set Report,
	fromAccidents: set Accident
}


sig Accident{
	position: lone Street,
	datetime: one Time
}

sig Suggestion{
	description: one Str,
	relatedviolation: one ViolationEnum
}

sig Violation{}

abstract sig ViolationEnum{}

one sig DoubleParking, DisableParking, BikeLaneParking extends ViolationEnum{}

fact usernameIsUnique{
  no disjoint u1, u2: User | u1.username = u2.username
}

fact emailIsUnique{
  no disjoint u1, u2: User | u1.email = u2.email
}

fact authorityIsUnique{
  no disjoint a1, a2: Authority | a1.CUU = a2.CUU
}

fact ImageRelatedOnlyToOneReport  {
	all i: Image | #picture.i = 1
}

fact LicenseplateRelatedOnlyToOneVehicle  {
	all l: Licenseplate | #vehicleplate.l = 1
}

fact noReportWithoutCityStatistic{
	all r: Report | #fromCityReports.r > 0
}

fact noSameStreetInTheSameCity{
	all s1, s2: Street | 
	s1.name = s2.name and s1 != s2
	implies s1.city != s2.city
}

pred reportFromSameCityInCityStatistic{

	all r: Report, c: City, cs: CityStatistic | 
	cs.relatedCity = c and r.position.city = c
	implies r in cs.fromCityReports
	
	all r: Report, cs: CityStatistic |
	r in cs.fromCityReports
	implies r.position.city = cs.relatedCity
}

fact userForStat{
	all u: User | #GroupedStatistics = 1
	implies #u.seeGroupedStatistics = 1
}

pred groupedStatisticsHasAllReportsAndAccindets{
	
	all gs: GroupedStatistics | #gs.fromReports > 0 or #gs.fromAccidents > 0

	all r: Report, gs: GroupedStatistics | r in gs.fromReports

	all a: Accident, gs: GroupedStatistics | a in gs.fromAccidents
}

fact reportCanOnlyExistIfHasLicenseplateInfo {

	all r: Report |  #r.picture.capturedlLicenseplate = 1 or #r.licenseplateHelper = 1

}

pred licenseplateHaveSameValueOfLicenseplateHelper{

	all r: Report | #r.picture.capturedlLicenseplate = 1 and #r.licenseplateHelper = 1
	implies r.picture.capturedlLicenseplate = r.licenseplateHelper
	

}

//world1
run groupedStatisticsHasAllReportsAndAccindets for 5 but exactly 1 GroupedStatistics, exactly 5 Report, exactly 2 Accident

//world2
run reportFromSameCityInCityStatistic for 4 but exactly 2 CityStatistic, exactly 2 Report, 2 City

//world 3
run licenseplateHaveSameValueOfLicenseplateHelper for 5 but exactly 3 Report





